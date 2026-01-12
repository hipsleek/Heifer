open Bindlib
open Unify
open Core.Syntax

exception Rewrite_failure

type rule = (term, staged_spec * staged_spec) mbinder

let rec prop_to_rule_aux (p : prop) =
  match p with
  | Conj _ -> invalid_arg "prop_to_rule_aux: PConj"
  | Implies _ -> invalid_arg "prop_to_rule_aux: PImplies"
  | Forall b ->
    let xs, p = unmbind b in
    let ms, lhs, rhs = prop_to_rule_aux p in
    (xs :: ms, lhs, rhs)
  | Subsumes (lhs, rhs) -> ([], lhs, rhs)
  | Unit | True | False | Nil | Emp | Var _ | Symbol _ | Int _ | Fun _ | Tuple _
  | Binop (_, _, _)
  | Unop (_, _)
  | Disj (_, _)
  | PointsTo (_, _)
  | SepConj (_, _)
  | Requires _ | Ensures _
  | Sequence (_, _)
  | Bind (_, _)
  | Apply (_, _)
  | Exists _ | Shift _ | Reset _ ->
    assert false

let prop_to_rule p =
  let ms, lhs, rhs = prop_to_rule_aux p in
  unbox
    (bind_mvar (Array.concat ms)
       (box_pair (box_staged_spec lhs) (box_staged_spec rhs)))

let rewrite_exact rule target : staged_spec =
  let uvars, (lhs, rhs) = unmbind rule in
  let sigma =
    try unify lhs target (TVSet.of_seq (Array.to_seq uvars))
    with Unification_failure -> raise Rewrite_failure
  in
  if TVMap.cardinal sigma <> Array.length uvars then raise Rewrite_failure;
  let args = Array.map (fun x -> TVMap.find x sigma) uvars in
  let rhs = unbox (bind_mvar uvars (box_staged_spec rhs)) in
  msubst rhs args

(** Traverse the target, and rewrite if possible.

    TODO: make this more efficient: repeated `unmbind` is inefficient *)
let rec rewrite rule target : staged_spec =
  try rewrite_exact rule target
  with Rewrite_failure ->
    (match target with
    | Requires p -> Requires p
    | Ensures p -> Ensures p
    | Sequence (s1, s2) -> Sequence (rewrite rule s1, rewrite rule s2)
    | Bind (s, b) -> Bind (rewrite rule s, rewrite_binder rule b)
    | Apply (f, t) -> Apply (f, t)
    | Disj (s1, s2) -> Disj (rewrite rule s1, rewrite rule s2)
    | Forall b -> Forall (rewrite_mbinder rule b)
    | Exists b -> Exists (rewrite_mbinder rule b)
    | Shift b -> Shift (rewrite_binder rule b)
    | Reset s -> Reset (rewrite rule s)
    | _ -> assert false)

and rewrite_binder rule target : (term, staged_spec) binder =
  let x, target = unbind target in
  unbox (bind_var x (box_staged_spec (rewrite rule target)))

and rewrite_mbinder rule target : (term, staged_spec) mbinder =
  let x, target = unmbind target in
  unbox (bind_mvar x (box_staged_spec (rewrite rule target)))
