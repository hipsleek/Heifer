open Bindlib
open Core.Syntax
open Core.Syntax_util
open Util.Strings
open Unify
open Tactic
open Tactics

let rec unify_list t ts uvars =
  match ts with
  | [] -> raise (Unification_failure "empty")
  | t' :: ts' -> (try unify t t' uvars with Unification_failure _ -> unify_list t ts' uvars)

let unify_heuristic_with uvars t ts =
  let uvars_set = TVSets.of_array uvars in
  try pure (unify_list t ts uvars_set) with Unification_failure msg -> fail msg

let unify_prop_heuristic uvars t =
  let* assumptions = get_assumptions in
  let assumptions = List.map snd (SMap.bindings assumptions) in
  unify_heuristic_with uvars t assumptions

let unify_hprop_heuristic uvars t = get_heap_assumptions >>= unify_heuristic_with uvars t

let unify_heuristic uvars t =
  if is_eq t then unify_prop_heuristic uvars t
  else if is_pointsto t then unify_hprop_heuristic uvars t
  else fail "heuristic failed"

let rec instantiation_heuristic f uvars target =
  match f target with
  | None -> fail "heuristic failed"
  | Some (t, target) ->
      let ok_case =
        let* sigma = unify_heuristic uvars t in
        unwrap (Subst.make_args uvars sigma) "heuristic failed"
      in
      let err_case _ = instantiation_heuristic f uvars (unwrap_term_opt target) in
      catch ok_case err_case

let forall_elim_heuristic =
  let* lhs = get_lhs in
  let* b = unwrap (open_forall_opt lhs) "not forall" in
  let uvars, lhs = unmbind b in
  let* args = instantiation_heuristic unseq_open_requires_opt uvars lhs in
  args <$ put_lhs (msubst b args)

let exists_intro_heuristic =
  let* rhs = get_rhs in
  let* b = unwrap (open_exists_opt rhs) "not forall" in
  let uvars, rhs = unmbind b in
  let* args = instantiation_heuristic unseq_open_ensures_opt uvars rhs in
  args <$ put_rhs (msubst b args)