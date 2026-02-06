open Core.Syntax
open Core.Pretty
open Core.Syntax_util
open Util.Strings
open Util.Lists
open Tactic
open Tactics
open Automation_heuristic

let rec repeat (tac : unit t) : unit t =
 fun s ->
  if List.is_empty s then Ok ((), s) else
  match tac s with
  | Error e -> Error e
  | Ok ((), s) -> repeat tac s

let intro_pure =
  let* n = fresh in
  let* () = Pures.intro_pure n in
  pure n

(* core automation tactic *)
type cert_tac =
  | Smt of term
  | Forall_intro
  | Exists_elim
  | Intro_pure of string
  | Elim_pure
  | Intro_heap
  | Elim_heap
  | Rewrite of string * term * cert list * cert
  | Disj_elim of cert * cert
  | Left
  | Right
  | Refl

and cert = cert_tac list

let rec pp_cert_tac ppf =
  let spaced_parens pp ppf v = Fmt.pf ppf "@[<1>( %a )@]" pp v in
  function
  | Smt t -> Fmt.pf ppf "prove () (* %a *)" pp_term t
  | Forall_intro -> Fmt.string ppf "forall_intro ()"
  | Exists_elim -> Fmt.string ppf "exists_elim ()"
  | Intro_pure n -> Fmt.pf ppf "intro_pure \"%s\"" n
  | Elim_pure -> Fmt.pf ppf "elim_pure ()"
  | Intro_heap -> Fmt.pf ppf "intro_heap ()"
  | Elim_heap -> Fmt.pf ppf "elim_heap ()"
  | Rewrite (n, t, c, k) ->
      Fmt.pf ppf "@[<v>rewrite \"%s\" (* %a *);" n pp_term t;
      (match c with
      | [] -> ()
      | [_] -> Fmt.pf ppf "@ %a" (Fmt.(list ~sep:(any ";@ ")) (spaced_parens pp_cert)) c
      | _ -> Fmt.pf ppf "@,%a" (Fmt.(list ~sep:(any ";@,")) (spaced_parens pp_cert)) c);
      Fmt.pf ppf "@,%a@]" pp_cert k
  | Disj_elim (c1, c2) ->
      Fmt.pf ppf "@[<v>disj_elim ();@,( @[<v 2>%a@] )@,( @[<v 2>%a )@]@]" pp_cert c1 pp_cert c2
  | Left -> Fmt.pf ppf "left ()"
  | Right -> Fmt.pf ppf "right ()"
  | Refl -> Fmt.pf ppf "refl ()"

and pp_cert ppf c = Fmt.pf ppf "@[<v>%a@]" Fmt.(list ~sep:(any ";@,") pp_cert_tac) c

let focus_and_solve_with tac =
  let* gs = get in
  match gs with
  | [] -> failf "no goals to solve"
  | g :: gs ->
      let* () = put [g] in
      let* r = tac in
      let* gs1 = get in
      (match gs1 with
      | [] ->
          let* () = put gs in
          pure r
      | _ ->
          Format.printf "%a@." Pstate.pp gs1;
          failf "failed to solve entirely")

let possible_rewrites2 self lemmas : cert_tac t list t =
  (* it's possible that a rewriting rule may be used multiple times
    e.g. IHs, so there is no attempt to use them only once for now *)
  let* hyps = get_assumptions <&> SMap.bindings in
  let rules = hyps @ lemmas in
  let rules =
    rules
    |> List.filter (fun (_n, s) ->
        try
          Rewrite.make_rule s |> ignore;
          true
        with Invalid_argument _ -> false)
  in
  let rules =
    rules
    |> List.map (fun (n, s) ->
        let* () = rewrite s in
        let* gs = get in
        let* sub : cert list =
          map_m
            (fun g ->
              let* () = put [g] in
              self ())
            gs
        in
        let* () = put [] in
        let init, tail = init_last sub in
        pure (Rewrite (n, s, init, tail)))
  in
  pure rules

let disj_elim self =
  let* () = Disj.disj_elim in
  let* gs = get in
  match gs with
  | l :: r :: rest ->
      let* () = put [l] in
      let* pl = self () in
      let* () = put [r] in
      let* pr = self () in
      let* () = put rest in
      pure (Disj_elim (pl, pr))
  | _ ->
      Format.printf "failed@.";
      failf "invalid state after disj, tactic error?"

let solve_cert ?(lemmas = []) : cert t =
  (* let* gs = get in *)
  (* with_focus Disj.disj_elim (fun gs1 -> pure ()) *)
  let rec solve () : cert t =
    let* g = get in
    (* Format.printf "solving %a@." Pstate.pp g; *)
    (* Format.printf "---@."; *)
    (* let _ : cert t list = possible_rewrites in *)
    match g with
    | [] ->
        (* Format.printf "return empty@."; *)
        pure []
    | _ :: _ ->
        let* possible_rewrites = possible_rewrites2 solve lemmas in
        let* pf =
          Simpl.simpl
          *> choices
               ([
                  (* debug "about to disj_elim" @@ *)
                  disj_elim solve (* >>> dbg "disj" *);
                  (* debug "about to forall_intro" @@ *)
                  Disj.left *> pure Left;
                  Disj.right *> pure Right;
                  forall_intro *> pure Forall_intro (* >>> dbg "forall intro" *);
                  (* debug "about to exists_elim" @@ *)
                  exists_elim *> pure Exists_elim (* >>> dbg "exists elim" *);
                  (* debug "about to intro_pure"@@ *)
                  (intro_pure >>= fun n -> pure (Intro_pure n) (* >>> dbg "intro pure" *));
                  Pures.elim_pure *> pure Elim_pure;
                  refl *> pure Refl;
                ]
               @ possible_rewrites
               @ [
                   (* debug "about to prove" @@ *)
                   get_goal <&> (fun g -> Smt g) <* prove (* >>> dbg "smt"; *);
                 ])
        in
        (* Format.printf "pf %a@." pp_cert_tac pf; *)
        let* r = solve () in
        (* Format.printf "solve returned %a@." pp_cert r; *)
        (* Format.printf "result is %a@." pp_cert (pf :: r); *)
        pure (pf :: r)
  in
  let* r = focus_and_solve_with (solve ()) in
  (* Format.printf "result %a@." pp_cert r; *)
  pure r

let make_rewrite (h, s) =
  try
    let rule = Rewrite.make_rule s in
    let lhs = Rewrite.get_rule_lhs rule in
    let rhs = Rewrite.get_rule_rhs rule in
    let rule = if subterm lhs rhs then Rewrite.swap_rule_direction rule else rule in
    Some (pre_rewrite rule *> dbg ("rewrite " ^ h))
  with Invalid_argument _ -> None

let make_rewrites =
  List.filter_map make_rewrite

let auto_rewrite : unit t =
  let* assumptions = get_assumptions in
  let rec visit = function
    | [] -> fail "no progress"
    | h :: rest ->
        match make_rewrite h with
        | None -> visit rest
        | Some rw -> catch rw (fun _ -> visit rest)
  in visit (SMap.bindings assumptions)

let string_of_term_array ts =
  String.concat ", " (List.map (fun t -> Format.asprintf "%a" Core.Pretty.pp_term t) (Array.to_list ts))

(* try to solve the current goal and any subgoals it generates *)
let simple ?(lemmas = []) =
  let solve =
    let lemma_rewrites = make_rewrites lemmas in
    let rec go () =
      repeat
        (Simpl.simpl
        *> choices
             ([
                refl *> dbg "refl";
                Disj.disj_elim *> dbg "disj_elim";
                Disj.left *> dbg "left" >>= go;
                Disj.right *> dbg "right" >>= go;
                forall_intro *> dbg "forall_intro";
                exists_elim *> dbg "exists_elim";
                (dbg "try forall_elim" *> forall_elim_heuristic >>= fun ts -> dbg ("forall_elim with args: " ^ string_of_term_array ts));
                (dbg "try exists_intro" *> exists_intro_heuristic >>= fun ts -> dbg ("exists_intro with args: " ^ string_of_term_array ts));
                (intro_pure $> ()) *> dbg "intro_pure";
                Heaps.intro_heap *> dbg "intro_heap";
                dbg "try elim_pure" *> Pures.elim_pure *> dbg "elim_pure";
                dbg "try elim_heap" *> Heaps.elim_heap *> dbg "elim_heap";
              ]
            @ [(dbg "try prove" >>= fun _ ->
                let* ps = get in
                dbg (Format.asprintf "current goals: %a" Pstate.pp ps) *> prove *> dbg "prove");
                ex_falso *> Pures.pure_solver *> dbg "ex_falso";
                auto_rewrite]
            @ lemma_rewrites))
    in go ()
  in
  () <$ try_ (focus_and_solve_with solve)
