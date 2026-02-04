open Core
open Core.Syntax
open Core.Pretty
open Util.Strings
open Util.Lists
open Tactic
open Tactics

let rec repeat (tac : unit t) : unit t =
 fun s ->
  match tac s with
  | Error _ ->
      (* Format.printf "repeat stopped@."; *)
      (* repeat never fails *)
      (* TODO repeat should stop when progress stops, not on failure? *)
      Ok ((), s)
  | Ok ((), s1) ->
      (* Format.printf "repeating@."; *)
      repeat tac s1

let maybe_prove_pure =
  let* g = get_goal in
  match g with
  | Subsumes _ -> prove
  | _ when Simply_typed.is_prop g -> prove
  | _ -> failf "doesn't look like a pure prop"

let intro_pure =
  let* n = fresh in
  let* () = Pure.intro_pure n in
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
        let* () = rewrite `Ltr s in
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
                  Pure.elim_pure *> pure Elim_pure;
                  refl *> pure Refl;
                ]
               @ possible_rewrites
               @ [
                   (* debug "about to prove" @@ *)
                   get_goal <&> (fun g -> Smt g) <* maybe_prove_pure (* >>> dbg "smt"; *);
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

let possible_rewrites : unit t list t =
  let* hyps = get_assumptions <&> SMap.bindings in
  pure
    (hyps
    |> List.filter_map (fun (_, s) ->
        match s with
        | Forall _ | Implies _ | Subsumes _ | Binop (Eq, _, _) ->
            (* Format.printf "chosen for rewrite %a@." pp_term s; *)
            Some (rewrite `Ltr s)
        | _ -> None))

(* try to solve the current goal and any subgoals it generates *)
let simple =
  let solve =
    let* possible_rewrites = possible_rewrites in
    repeat
      (Simpl.simpl
      *> choices
           ([
              Disj.disj_elim *> dbg "disj_elim";
              Disj.left *> dbg "left";
              Disj.right *> dbg "right";
              forall_intro *> dbg "forall_intro";
              exists_elim *> dbg "exists_elim";
              (intro_pure $> ()) *> dbg "intro pure";
              Pure.elim_pure *> dbg "elim_pure";
              refl *> dbg "refl";
            ]
           @ [maybe_prove_pure *> dbg "prove pure"]
           @ possible_rewrites))
  in
  () <$ try_ (focus_and_solve_with solve)
