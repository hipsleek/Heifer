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
  if List.is_empty s then Ok ((), s)
  else
    match tac s with
    | Error e -> Error e
    | Ok ((), s) -> repeat tac s

let intro_pure =
  let* n = fresh ~prefix:"H" in
  let* () = Pures.intro_pure n in
  pure n

let dbg_state =
  let* ps = get in
  dbg (Format.asprintf "current goals: %a" Pstate.pp ps)

(* core automation tactic *)
type cert_tac =
  | Smt of term
  | Forall_intro
  | Exists_elim
  | Forall_elim of term array
  | Exists_intro of term array
  | Intro_pure of string
  | Elim_pure
  | Intro_heap
  | Elim_heap
  | Rewrite of string * term * cert list * cert
  | Disj_elim of cert * cert
  | Left of cert
  | Right of cert
  | Refl
  | Ex_falso

and cert = cert_tac list

module Cert = struct
  let smt t = Smt t
  let forall_elim ts = Forall_elim ts
  let exists_intro ts = Exists_intro ts
  let intro_pure name = Intro_pure name
  let left c = Left c
  let right c = Right c
end

let rec pp_cert_tac ppf =
  let spaced_parens pp ppf v = Fmt.pf ppf "@[<1>( %a )@]" pp v in
  function
  | Smt t -> Fmt.pf ppf "prove () (* %a *)" pp_term t
  | Forall_intro -> Fmt.string ppf "forall_intro ()"
  | Exists_elim -> Fmt.string ppf "exists_elim ()"
  | Forall_elim ts -> Fmt.pf ppf "forall_elim %a" (Fmt.array ~sep:(Fmt.any "; ") pp_term) ts
  | Exists_intro ts -> Fmt.pf ppf "exists_elim %a" (Fmt.array ~sep:(Fmt.any "; ") pp_term) ts
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
  | Left c -> Fmt.pf ppf "@[<v>left ();@,%a@]" pp_cert c
  | Right c -> Fmt.pf ppf "@[<v>right ();@,%a@]" pp_cert c
  | Refl -> Fmt.pf ppf "refl ()"
  | Ex_falso -> Fmt.pf ppf "@[<v>ex_falso ();@,pure_solver ()]@"

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
      | [] -> r <$ put gs
      | _ ->
          Format.printf "%a@." Pstate.pp gs1;
          failf "failed to solve entirely")

let make_rewrite t =
  try
    let rule = Rewrite.make_rule t in
    let lhs = Rewrite.get_rule_lhs rule in
    let rhs = Rewrite.get_rule_rhs rule in
    let rule = if subterm lhs rhs then Rewrite.swap_rule_direction rule else rule in
    Some (pre_rewrite rule)
  with Invalid_argument _ -> None

let possible_rewrites2 self lemmas : cert_tac t list =
  (* it's possible that a rewriting rule may be used multiple times
    e.g. IHs, so there is no attempt to use them only once for now *)
  List.filter_map (fun (n, t) ->
    match make_rewrite t with
    | None -> None
    | Some rw ->
        let tactic =
          let* _ = rw in
          let* ps = get in
          let* sub = map_m (fun p -> put [p] >>= self) ps in
          let init, tail = init_last sub in
          pure (Rewrite (n, t, init, tail))
        in
        Some tactic)
    lemmas

let disj_elim self =
  let* () = Disj.disj_elim in
  let* gs = get in
  match gs with
  | [l; r] ->
      let* () = put [l] in
      let* pl = self () in
      let* () = put [r] in
      let* pr = self () in
      pure (Disj_elim (pl, pr))
  | _ ->
      Format.printf "failed@.";
      failf "invalid state after disj, tactic error?"

let auto_rewrite_with self =
  let* assumptions = get_assumptions in
  let rec visit = function
    | [] -> fail "no progress"
    | (h, t) :: rest ->
        match make_rewrite t with
        | None -> visit rest
        | Some rw ->
            let tactic =
              let* _ = rw in
              let* ps = get in
              let* sub = map_m (fun p -> put [p] >>= self) ps in
              let init, tail = init_last sub in
              pure (Rewrite (h, t, init, tail))
            in
            catch tactic (fun _ -> visit rest)
  in
  visit (SMap.bindings assumptions)

let solve_cert ?(lemmas = []) : cert t =
  let rec solve () : cert t =
    let lemma_rewrites = possible_rewrites2 solve lemmas in
    let* g = get in
    (* Format.printf "---@."; *)
    (* let _ : cert t list = possible_rewrites in *)
    match g with
    | [] ->
        (* Format.printf "return empty@."; *)
        pure []
    | _ ->
        (* Format.printf "#goals: %d@." (List.length g); *)
        let* pf =
          Simpl.simpl
          *> choices
               ([
                  Refl <$ refl;
                  disj_elim solve (* >>> dbg "disj" *);
                  Cert.left <$> (Disj.left >>= solve);
                  Cert.right <$> (Disj.right >>= solve);
                  Forall_intro <$ forall_intro (* >>> dbg "forall intro" *);
                  Exists_elim <$ exists_elim (* >>> dbg "exists elim" *);
                  Cert.forall_elim <$> forall_elim_heuristic;
                  Cert.exists_intro <$> exists_intro_heuristic;
                  Cert.intro_pure <$> intro_pure (* >>> dbg "intro pure" *);
                  Intro_heap <$ Heaps.intro_heap;
                  Elim_pure <$ Pures.elim_pure;
                  Elim_heap <$ Heaps.elim_heap;
                  Cert.smt <$> get_goal <* prove (* >>> dbg "smt"; *);
                  Ex_falso <$ (ex_falso *> Pures.pure_solver);
                  auto_rewrite_with solve
                 ]
                @ lemma_rewrites)
        in
        (* Format.printf "pf %a@." pp_cert_tac pf; *)
        let* r = solve () in
        pure (pf :: r)
  in
  focus_and_solve_with (solve ())

let make_rewrites =
  List.filter_map (fun (h, t) -> Option.map (fun rw -> rw *> dbg ("rewrite " ^ h)) (make_rewrite t))

let auto_rewrite : unit t =
  let* assumptions = get_assumptions in
  let rec visit = function
    | [] -> fail "no progress"
    | (h, t) :: rest ->
        match make_rewrite t with
        | None -> visit rest
        | Some rw ->
            let tactic =
              let* _ = rw in
              dbg ("rewrite " ^ h)
            in
            catch tactic (fun _ -> visit rest)
  in visit (SMap.bindings assumptions)

let string_of_term_array ts =
  String.concat ", "
    (List.map (fun t -> Format.asprintf "%a" Core.Pretty.pp_term t) (Array.to_list ts))

(* try to solve the current goal and any subgoals it generates *)
let simple ?(lemmas = []) =
  let lemma_rewrites = make_rewrites lemmas in
  let solve =
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
                ( dbg "try forall_elim" *> forall_elim_heuristic >>= fun ts ->
                  dbg ("forall_elim with args: " ^ string_of_term_array ts) );
                ( dbg "try exists_intro" *> exists_intro_heuristic >>= fun ts ->
                  dbg ("exists_intro with args: " ^ string_of_term_array ts) );
                intro_pure *> dbg "intro_pure";
                Heaps.intro_heap *> dbg "intro_heap";
                dbg "try elim_pure" *> Pures.elim_pure *> dbg "elim_pure";
                dbg "try elim_heap" *> Heaps.elim_heap *> dbg "elim_heap";
                dbg "try prove" *> dbg_state *> prove *> dbg "prove";
                ex_falso *> Pures.pure_solver *> dbg "ex_falso";
                auto_rewrite;
            ]
            @ lemma_rewrites))
    in go ()
  in
  () <$ try_ (focus_and_solve_with solve)
