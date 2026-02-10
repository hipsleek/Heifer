open Util
open Core.Syntax
open Core.Pretty
open Core.Syntax_util
open Util.Strings
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
  let* name = fresh ~prefix:"H" in
  name <$ Pures.intro_pure name

let dbg_state =
  let* state = get in
  dbg (Format.asprintf "current state: %a" Pstate.pp state)

(* core automation tactic *)
type cert =
  | Smt of term
  | Forall_intro of cert
  | Exists_elim of cert
  | Forall_elim of term list * cert
  | Exists_intro of term list * cert
  | Intro_pure of string * cert
  | Elim_pure of cert
  | Intro_heap of cert
  | Elim_heap of cert
  | Rewrite of string * term * cert list * cert
  | Disj_elim of cert * cert
  | Left of cert
  | Right of cert
  | Refl
  | Ex_falso

module Cert = struct
  let smt t = Smt t
  let forall_intro c = Forall_intro c
  let exists_elim c = Exists_elim c
  let forall_elim ts c = Forall_elim (ts, c)
  let exists_intro ts c = Exists_intro (ts, c)
  let intro_pure name c = Intro_pure (name, c)
  let elim_pure c = Elim_pure c
  let intro_heap c = Intro_heap c
  let elim_heap c = Elim_heap c
  let rewrite name t cs c = Rewrite (name, t, cs, c)
  let disj_elim c1 c2 = Disj_elim (c1, c2)
  let left c = Left c
  let right c = Right c
  let refl = Refl
  let ex_falso = Ex_falso
end

let rec pp_cert ppf =
  let spaced_parens pp ppf = Fmt.pf ppf "@[<1>( %a )@]" pp in
  let quoted pp ppf = Fmt.pf ppf "\"%a\"" pp in
  let quoted_list pp ppf = Fmt.pf ppf "[%a]" (Fmt.list ~sep:(Fmt.any "; ") (quoted pp)) in
  function
  | Smt t -> Fmt.pf ppf "prove () (* %a *)" pp_term t
  | Forall_intro c -> Fmt.pf ppf "@[<v>forall_intro ();@,%a@]" pp_cert c
  | Exists_elim c -> Fmt.pf ppf "@[<v>exists_elim ();@,%a@]" pp_cert c
  | Forall_elim (ts, c) ->
      Fmt.pf ppf "@[<v>forall_elim %a;@,%a@]" (quoted_list pp_term) ts pp_cert c
  | Exists_intro (ts, c) ->
      Fmt.pf ppf "@[<v>exists_intro %a;@,%a@]" (quoted_list pp_term) ts pp_cert c
  | Intro_pure (name, c) -> Fmt.pf ppf "@[<v>intro_pure \"%s\";@,%a@]" name pp_cert c
  | Elim_pure c -> Fmt.pf ppf "@[<v>elim_pure ();@,%a@]" pp_cert c
  | Intro_heap c -> Fmt.pf ppf "@[<v>intro_heap ();@,%a@]" pp_cert c
  | Elim_heap c -> Fmt.pf ppf "@[<v>elim_heap ();@,%a@]" pp_cert c
  | Rewrite (n, t, c, k) ->
      Fmt.pf ppf "@[<v>rewrite \"%s\" (* %a *);" n pp_term t;
      (match c with
      | [] -> ()
      | [_] -> Fmt.pf ppf "@ %a" (Fmt.(list ~sep:(any ";@ ")) (spaced_parens pp_cert)) c
      | _ -> Fmt.pf ppf "@,%a" (Fmt.(list ~sep:(any ";@,")) (spaced_parens pp_cert)) c);
      Fmt.pf ppf "@,%a@]" pp_cert k
  | Disj_elim (c1, c2) ->
      Fmt.pf ppf "@[<v>disj_elim ();@,( @[<v 2>%a@] )@,( @[<v 2>%a@] )@]" pp_cert c1 pp_cert c2
  | Left c -> Fmt.pf ppf "@[<v>left ();@,%a@]" pp_cert c
  | Right c -> Fmt.pf ppf "@[<v>right ();@,%a@]" pp_cert c
  | Refl -> Fmt.pf ppf "@[<v>refl ();@]"
  | Ex_falso -> Fmt.pf ppf "@[<v>ex_falso ();@,pure_solver ()@]"

let focus tactic =
  let* ps = get in
  match ps with
  | [] -> fail "no more goal"
  | p :: ps ->
      (* let* _ = dbg (Format.asprintf "number of remaining goals: %d@." (List.length ps + 1)) in *)
      let* _ = put [p] in
      let* r = tactic in
      r <$ put ps

let make_rewrite t =
  try
    let rule = Rewrite.make_rule t in
    let lhs = Rewrite.get_rule_lhs rule in
    let rhs = Rewrite.get_rule_rhs rule in
    let rule = if subterm lhs rhs then Rewrite.swap_rule_direction rule else rule in
    Some (pre_rewrite rule)
  with Invalid_argument _ -> None

let make_lemma_rewrites =
  List.filter_map (fun assumption ->
      let _, t = assumption in
      match make_rewrite t with
      | None -> None
      | Some tactic -> Some (assumption <$ tactic))

type 'a strategy =
  | Done : 'a t -> 'a strategy
  | More : 'b t * ('b -> 'a t) -> 'a strategy

let rec try_and_cut = function
  | [] -> fail "no progress"
  | Done tactic :: rest -> catch tactic (fun _ -> try_and_cut rest)
  | More (tactic, action) :: rest ->
      let* r = try_ tactic in
      (match r with
      | Ok v -> action v
      | Error _ -> try_and_cut rest)

let auto_rewrite lemma_rewrites =
  let* assumptions = get_assumptions in
  let rec visit = function
    | [] -> choices lemma_rewrites
    | assumption :: rest ->
        let _, t = assumption in
        (match make_rewrite t with
        | None -> visit rest
        | Some tactic -> catch (assumption <$ tactic) (fun _ -> visit rest))
  in
  visit (SMap.bindings assumptions)

module SolveCert = struct
  let after_disj_elim solve () =
    let* ps = get in
    match ps with
    | [_; _] ->
        let* pl = focus (solve ()) in
        let+ pr = focus (solve ()) in
        Cert.disj_elim pl pr
    | _ -> fail "invalid state after disj_elim"

  let after_left solve ps =
    catch (Cert.left <$> solve ()) (fun _ -> Cert.right <$> put ps *> Disj.right *> solve ())

  let after_auto_rewrite solve (name, t) =
    (* let* _ = dbg "[after_auto_rewrite]\n" in *)
    (* let* _ = dbg_state in *)
    let* ps = get in
    let+ cs = map_m (fun _ -> focus (solve ())) ps in
    let cs, c = Lists.unsnoc cs in
    Cert.rewrite name t cs c
end

let solve_cert ?(lemmas = []) ?(depth = !Proof_options.auto_proof_depth) : cert t =
  let lemma_rewrites = make_lemma_rewrites lemmas in
  let rec solve depth () =
    let* _ = guard (depth > 0) "maximum proof depth reached" in
    let solve = solve (depth - 1) in
    let* _ = Simpl.simpl in
    try_and_cut
      [
        Done (Cert.refl <$ refl);
        More (Disj.disj_elim, SolveCert.after_disj_elim solve);
        More (get <* Disj.left, SolveCert.after_left solve);
        More (forall_intro, fun _ -> Cert.forall_intro <$> solve ());
        More (exists_elim, fun _ -> Cert.exists_elim <$> solve ());
        More (forall_elim_heuristic, fun ts -> Cert.forall_elim (Array.to_list ts) <$> solve ());
        More (exists_intro_heuristic, fun ts -> Cert.exists_intro (Array.to_list ts) <$> solve ());
        More (intro_pure, fun name -> Cert.intro_pure name <$> solve ());
        More (Heaps.intro_heap, fun _ -> Cert.intro_heap <$> solve ());
        More (Pures.elim_pure, fun _ -> Cert.elim_pure <$> solve ());
        More (Heaps.elim_heap, fun _ -> Cert.elim_heap <$> solve ());
        Done (Cert.smt <$> get_goal <* prove);
        Done (Cert.ex_falso <$ ex_falso *> Pures.pure_solver);
        More (auto_rewrite lemma_rewrites, SolveCert.after_auto_rewrite solve);
      ]
  in
  focus (solve depth ())

let simple ?(lemmas = []) ?(depth = !Proof_options.auto_proof_depth) =
  () <$ solve_cert ~lemmas ~depth

module DbgSimple = struct
  let after_disj_elim solve () =
    let* _ = dbg "disj_elim" in
    let* ps = get in
    match ps with
    | [_; _] ->
        let* _ = focus (solve ()) in
        let+ _ = focus (solve ()) in
        ()
    | _ -> fail "invalid state after disj_elim"

  let after_left solve ps =
    let* _ = dbg "left" in
    catch (solve ()) (fun _ -> put ps *> Disj.right *> dbg "right" *> solve ())

  let after_auto_rewrite solve (name, t) =
    let* _ = dbg (Format.asprintf "rewrite %s: %a" name pp_term t) in
    let* ps = get in
    iter_m (fun _ -> focus (solve ())) ps
end

(* try to solve the current goal and any subgoals it generates *)
let dbg_simple ?(lemmas = []) ?(depth = !Proof_options.auto_proof_depth) =
  let lemma_rewrites = make_lemma_rewrites lemmas in
  let rec solve depth () =
    let* _ = guard (depth > 0) "maximum proof depth reached" in
    let solve = solve (depth - 1) in
    let* _ = Simpl.simpl in
    try_and_cut
      [
        Done (refl *> dbg "refl");
        More (Disj.disj_elim, DbgSimple.after_disj_elim solve);
        More (get <* Disj.left, DbgSimple.after_left solve);
        More (forall_intro, fun _ -> dbg "forall_intro" *> solve ());
        More (exists_elim, fun _ -> dbg "exists_elim" *> solve ());
        More (forall_elim_heuristic, fun _ -> dbg "forall_elim" *> solve ());
        More (exists_intro_heuristic, fun _ -> dbg "exists_intro" *> solve ());
        More (intro_pure, fun _ -> dbg "intro_pure" *> solve ());
        More (Heaps.intro_heap, fun _ -> dbg "intro_heap" *> solve ());
        More (Pures.elim_pure, fun _ -> dbg "elim_pure" *> solve ());
        More (Heaps.elim_heap, fun _ -> dbg "elim_heap" *> solve ());
        Done (dbg_state *> prove *> dbg "prove");
        Done (ex_falso *> Pures.pure_solver *> dbg "ex_falso");
        More (dbg_state *> auto_rewrite lemma_rewrites, DbgSimple.after_auto_rewrite solve);
      ]
  in
  focus (solve depth ())
