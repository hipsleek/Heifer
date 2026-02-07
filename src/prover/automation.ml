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
  let spaced_parens pp ppf v = Fmt.pf ppf "@[<1>( %a )@]" pp v in
  function
  | Smt t -> Fmt.pf ppf "prove () (* %a *)" pp_term t
  | Forall_intro c -> Fmt.pf ppf "@[<v>forall_intro ();@,%a@]" pp_cert c
  | Exists_elim c -> Fmt.pf ppf "@[<v>exists_elim ();@,%a@]" pp_cert c
  | Forall_elim (ts, c) -> Fmt.pf ppf "@[<v>forall_elim %a;@,%a@]" (Fmt.list ~sep:(Fmt.any "; ") pp_term) ts pp_cert c
  | Exists_intro (ts, c) -> Fmt.pf ppf "@[<v>exists_intro %a;@,%a@]" (Fmt.list ~sep:(Fmt.any "; ") pp_term) ts pp_cert c
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
      let* _ = dbg (Format.asprintf "number of remaining goals: %d@." (List.length ps + 1)) in
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
  List.filter_map
    (fun assumption ->
      let (name, t) = assumption in
      match make_rewrite t with
      | None -> None
      | Some tactic -> Some (let* _ = dbg (Format.asprintf "trying to rewrite with assumption %s: %a" name pp_term t) in assumption <$ tactic))

(* let possible_rewrites2 self lemmas : cert t list =
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
    lemmas *)

type 'a strategy =
  | Done : 'a t -> 'a strategy
  | More : 'b t * ('b -> 'a t) -> 'a strategy

let rec try_and_cut = function
  | [] -> fail "no progress"
  | Done tactic :: rest ->
      catch tactic (fun _ -> try_and_cut rest)
  | More (tactic, action) :: rest ->
      let* r = try_ tactic in
      match r with
      | Ok v -> action v
      | Error _ -> try_and_cut rest

let auto_rewrite lemma_rewrites =
  let* assumptions = get_assumptions in
  let rec visit = function
    | [] -> choices lemma_rewrites
    | assumption :: rest ->
        let (name, t) = assumption in
        match make_rewrite t with
        | None -> visit rest
        | Some tactic ->
            let* _ = dbg (Format.asprintf "trying to rewrite with assumption %s: %a" name pp_term t) in
            catch (assumption <$ tactic) (fun _ -> visit rest)
  in visit (SMap.bindings assumptions)

let after_disj_elim solve () =
  let* ps = get in
  match ps with
  | [_; _] ->
      let* pl = focus (solve ()) in
      let+ pr = focus (solve ()) in
      Cert.disj_elim pl pr
  | _ -> fail "invalid state after disj_elim"

let after_left solve ps =
  catch (Cert.left <$> solve ()) (fun _ ->
    Cert.right <$> put ps *> dbg "[after left]\n" *> dbg_state *> Disj.right *> solve ())

let after_auto_rewrite solve (name, t) =
  let* _ = dbg "[after_auto_rewrite]\n" in
  let* _ = dbg_state in
  let* ps = get in
  let+ cs = map_m (fun _ -> focus (solve ())) ps in
  let cs, c = Lists.unsnoc cs in
  Cert.rewrite name t cs c

let solve_cert ?(lemmas = []) : cert t =
  let lemma_rewrites = make_lemma_rewrites lemmas in
  let rec solve ?(depth = 100) () =
    let* _ = guard (depth > 0) "maximum proof depth reached" in
    let solve = solve ~depth:(depth - 1) in
    let* _ = Simpl.simpl in
    try_and_cut
      [
        Done (Cert.refl <$ refl);
        More (Disj.disj_elim, after_disj_elim solve);
        More (get <* Disj.left, after_left solve);
        More (forall_intro, fun _ -> Cert.forall_intro <$> solve ());
        More (exists_elim, fun _ -> Cert.exists_elim <$> solve ());
        More (forall_elim_heuristic, fun ts -> Cert.forall_elim (Array.to_list ts) <$> solve ());
        More (exists_intro_heuristic, fun ts -> Cert.exists_intro (Array.to_list ts) <$> solve ());
        More (intro_pure, fun name -> Cert.intro_pure name <$> solve ());
        More (Heaps.intro_heap, fun _ -> Cert.intro_heap <$> solve ());
        More (Pures.elim_pure, fun _ -> Cert.elim_pure <$> solve ());
        More (Heaps.elim_heap, fun _ -> Cert.elim_heap <$> solve ());
        Done (Cert.smt <$> get_goal <* dbg "[prove]\n" <* dbg_state <* prove);
        Done (Cert.ex_falso <$ ex_falso *> Pures.pure_solver);
        More (auto_rewrite lemma_rewrites, after_auto_rewrite solve)
      ]
  in
  focus (solve ())

(* let string_of_term_array ts =
  String.concat ", "
    (List.map (fun t -> Format.asprintf "%a" Core.Pretty.pp_term t) (Array.to_list ts)) *)

(* try to solve the current goal and any subgoals it generates *)
let simple ?(lemmas = []) =
  () <$ solve_cert ~lemmas
  (* let lemma_rewrites = make_lemma_rewrites lemmas in
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
            ]
            @ lemma_rewrites))
    in go ()
  in
  () <$ try_ (focus solve) *)
