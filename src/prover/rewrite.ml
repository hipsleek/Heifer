open Bindlib
open Unify
open Core.Syntax

exception Rewrite_failure

(** Rewrite rules are conditional and have a left and right side. All may refer
    to bound variables. *)
type rule = (term, prop list * (staged_spec * staged_spec)) mbinder

let rec prop_to_rule_aux p ms side =
  match p with
  | Forall b ->
      let xs, p = unmbind b in
      prop_to_rule_aux p (xs :: ms) side
  | Implies (a, b) -> prop_to_rule_aux b ms (a :: side)
  | Subsumes (lhs, rhs) -> (List.rev ms, List.rev side, lhs, rhs)
  | Binop (Eq, lhs, rhs) -> (List.rev ms, List.rev side, lhs, rhs)
  | _ -> failwith "cannot convert prop into a conditional rewrite rule"

let prop_to_rule p =
  let ms, side, lhs, rhs = prop_to_rule_aux p [] [] in
  let side = box_list (List.map box_term side) in
  let lhs = box_term lhs in
  let rhs = box_term rhs in
  unbox (bind_mvar (Array.concat ms) (box_pair side (box_pair lhs rhs)))

(** Rewrite the target at the top level, either raising on failure or returning
    the rewritten target and instantiated subgoals *)
let rewrite_exact rule target =
  let uvars, (side, (lhs, rhs)) = unmbind rule in
  let sigma =
    try unify lhs target (TVSet.of_seq (Array.to_seq uvars))
    with Unification_failure -> raise Rewrite_failure
  in
  if TVMap.cardinal sigma <> Array.length uvars then raise Rewrite_failure;
  let args = Array.map (fun x -> TVMap.find x sigma) uvars in
  let rhs = unbox (bind_mvar uvars (box_term rhs)) in
  let rhs = msubst rhs args in
  let side =
    List.map
      (fun a ->
        let a = unbox (bind_mvar uvars (box_term a)) in
        let a = msubst a args in
        a)
      side
  in
  (rhs, side)

(** Traverse the target and rewrite using the given rule everywhere in it. If
    the rewrite succeeds, accumulates side conditions using a mutable reference.

    Implementation notes:

    - This could be done with a writer monad instead, but would be much more
      verbose.
    - This is unlike Rocq's rewriting using evars, where all occurrences subject
      to one evar instantiation are rewritten. The consequence is that a fixed
      number of subgoals is produced from the side conditions. In contarst, our
      scheme produces a number of side conditions/subgoals depending on the
      number of occurrences rewritten. This is because the instantiations are
      only discovered during traversal. *)
let rec rewrite_aux ~side rule target =
  try
    let t, c = rewrite_exact rule target in
    side := c :: !side;
    t
  with Rewrite_failure ->
    (match target with
    | Var _ | Symbol _ | Unit | True | False | Int _ | Nil | Emp -> target
    | Fun b -> Fun (rewrite_mbinder ~side rule b)
    | Tuple ts -> Tuple (rewrite_list ~side rule ts)
    | Binop (op, t1, t2) ->
        Binop (op, rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | Unop (op, t) -> Unop (op, rewrite_aux ~side rule t)
    | Conj (t1, t2) ->
        Conj (rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | Implies (t1, t2) ->
        Implies (rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | Subsumes (t1, t2) ->
        Subsumes (rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | PointsTo (t1, t2) ->
        PointsTo (rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | SepConj (t1, t2) ->
        SepConj (rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | Requires t -> Requires (rewrite_aux ~side rule t)
    | Ensures t -> Ensures (rewrite_aux ~side rule t)
    | Sequence (t1, t2) ->
        Sequence (rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | Bind (t, b) -> Bind (rewrite_aux ~side rule t, rewrite_binder ~side rule b)
    | Apply (f, t) -> Apply (rewrite_aux ~side rule f, rewrite_list ~side rule t)
    | Disj (t1, t2) ->
        Disj (rewrite_aux ~side rule t1, rewrite_aux ~side rule t2)
    | Forall b -> Forall (rewrite_mbinder ~side rule b)
    | Exists b -> Exists (rewrite_mbinder ~side rule b)
    | Shift b -> Shift (rewrite_binder ~side rule b)
    | Reset t -> Reset (rewrite_aux ~side rule t))

and rewrite_list ~side rule target = List.map (rewrite_aux ~side rule) target

and rewrite_binder ~side rule target =
  let x, target = unbind target in
  unbox (bind_var x (box_term (rewrite_aux ~side rule target)))

and rewrite_mbinder ~side rule target =
  let x, target = unmbind target in
  unbox (bind_mvar x (box_term (rewrite_aux ~side rule target)))

let rewrite rule target =
  let side_conditions = ref [] in
  let t = rewrite_aux ~side:side_conditions rule target in
  (t, List.concat !side_conditions)
