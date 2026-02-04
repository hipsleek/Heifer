open Bindlib
open Core
open Core.Syntax
open Core.Syntax_util
open Util.Strings
open Unify
open Tactic
open Tactics

let rec unify_list t ts uvars =
  match ts with
  | [] -> raise (Unification_failure "empty")
  | t' :: ts' ->
      try unify t t' uvars
      with Unification_failure _ -> unify_list t ts' uvars

let unify_heuristic_with uvars t ts =
  let uvars_set = TVSets.of_array uvars in
  try pure (unify_list t ts uvars_set)
  with Unification_failure msg -> fail msg

let unify_prop_heuristic uvars t =
  let* assumptions = get_assumptions in
  let assumptions = List.map snd (SMap.bindings assumptions) in
  unify_heuristic_with uvars t assumptions

let unify_hprop_heuristic uvars t =
  get_heap_assumptions >>= unify_heuristic_with uvars t

let unify_heuristic uvars t =
  if Simply_typed.is_prop t then unify_prop_heuristic uvars t
  else if Simply_typed.is_hprop t then unify_hprop_heuristic uvars t
  else fail "heuristic failed"

let instantiation_heuristic uvars t =
  let* sigma = unify_heuristic uvars t in
  unwrap (Subst.make_args uvars sigma) "heuristic failed"

let forall_elim_heuristic =
  let* lhs = get_lhs in
  let* b = unwrap (open_forall_opt lhs) "not forall" in
  let uvars, lhs = unmbind b in
  let* t, _ = unwrap (unseq_open_requires_opt lhs) "not requires" in
  let* args = instantiation_heuristic uvars t in
  put_lhs (msubst b args)

let exists_intro_heuristic =
  let* rhs = get_rhs in
  let* b = unwrap (open_exists_opt rhs) "not forall" in
  let uvars, rhs = unmbind b in
  let* t, _ = unwrap (unseq_open_ensures_opt rhs) "not ensures" in
  let* args = instantiation_heuristic uvars t in
  put_rhs (msubst b args)
