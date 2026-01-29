open Bindlib
open Unify
open Util
open Core.Syntax
open Core.Syntax_util

exception Rewrite_failure of string

type rule_direction =
  | Direction_ltr
  | Direction_rtl

type rule_relation =
  | Relation_eq
  | Relation_subsumes

type conditional_rule = term mvar * term list * term * term

type rule = term mvar * term * term

let prop_to_conditional_rule direction t =
  let open Snoc_list in
  let rec visit mvars conditions = function
    | Forall b ->
        let xs, t = unmbind b in
        visit (Snoc (mvars, xs)) conditions t
    | Implies (t1, t2) -> visit mvars (Snoc (conditions, t1)) t2
    | Subsumes (t1, t2) | Binop (Eq, t1, t2) -> (mvars, conditions, t1, t2)
    | _ -> failwith "cannot convert term into a conditional rewrite rule"
  in
  let mvars, conditions, t1, t2 = visit Lin Lin t in
  let t1, t2 =
    match direction with
    | Direction_ltr -> (t1, t2)
    | Direction_rtl -> (t2, t1)
  in
  let uvars = Array.concat (to_list mvars) in
  let conditions = to_list conditions in
  (uvars, conditions, t1, t2)

let rule_to_conditional_rule (uvars, t1, t2) = (uvars, [], t1, t2)

module Monad : sig
  type 'a t
  val run : 'a t -> term TVMap.t -> 'a * term TVMap.t * int
  val pure : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val lift2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val get : term TVMap.t t
  val put : term TVMap.t -> unit t
  val modify : (term TVMap.t -> term TVMap.t) -> unit t
  val tell : int -> unit t
end = struct
  type 'a t = term TVMap.t -> 'a * term TVMap.t * int
  let run m = m
  let pure x sigma = (x, sigma, 0)

  let map f m sigma =
    let x, sigma, n = m sigma in
    (f x, sigma, n)

  let lift2 f m1 m2 sigma =
    let x, sigma, n1 = m1 sigma in
    let y, sigma, n2 = m2 sigma in
    (f x y, sigma, n1 + n2)

  let bind m f sigma =
    let x, sigma, n1 = m sigma in
    let y, sigma, n2 = f x sigma in
    (y, sigma, n1 + n2)

  let ( <$> ) = map
  let ( >>= ) = bind
  let ( let+ ) m f = map f m
  let ( let* ) = bind
  let get sigma = (sigma, sigma, 0)
  let put sigma _ = ((), sigma, 0)
  let modify f sigma = ((), f sigma, 0)
  let tell n sigma = ((), sigma, n)
end

let uvars_of_conditions =
  List.fold_left pre_get_vars TVSet.empty

(** Rewrite the target at the top level, either raising on failure or returning the rewritten target *)
let rewrite_exact rule target =
  let uvars, lhs, rhs = rule in
  let sigma =
    match unify lhs target (TVSet.of_seq (Array.to_seq uvars)) with
    | sigma -> sigma
    | exception Unification_failure msg -> raise (Rewrite_failure msg)
  in
  if TVMap.cardinal sigma <> Array.length uvars then
    (* this condition means variables could not be instantiated *)
    raise (Rewrite_failure "could not instantiate all unification variables");
  let args = Array.map (fun x -> TVMap.find x sigma) uvars in
  let rhs = mgeneralize uvars rhs in
  msubst rhs args

(* let rewrite_exact_conditional conditional_rule target =
  let uvars, conditions, lhs, rhs = conditional_rule in
  let sigma =
    match unify lhs target (TVSet.of_seq (Array.to_seq uvars)) with
    | sigma -> sigma
    | exception Unification_failure msg -> raise (Rewrite_failure msg)
  in
  if TVMap.cardinal sigma <> Array.length uvars then
    (* this condition means variables could not be instantiated *)
    raise (Rewrite_failure "could not instantiate all unification variables");
  let args = Array.map (fun x -> TVMap.find x sigma) uvars in
  (** instantiate condition, but we need to check bindings? *)
  let conditions = failwith "todo: instantiate conditions" in
  let rhs = mgeneralize uvars rhs in
  let rhs = msubst rhs args in
  (rhs, conditions) *)

let rewrite_exact_assoc rule target =
  let uvars, lhs, rhs = rule in
  let sigma, frame =
    match unify_assoc lhs target (TVSet.of_seq (Array.to_seq uvars)) with
    | sigma, None -> sigma, Fun.id
    | sigma, Some frame -> (sigma, frame)
    | exception Unification_failure msg -> raise (Rewrite_failure msg)
  in
  if TVMap.cardinal sigma <> Array.length uvars then
    (* this condition means variables could not be instantiated *)
    raise (Rewrite_failure "could not instantiate all unification variables");
  let args = Array.map (fun x -> TVMap.find x sigma) uvars in
  let rhs = mgeneralize uvars rhs in
  frame (msubst rhs args)

(** Traverse the target and rewrite using the given rule everywhere in it. If the rewrite succeeds,
    accumulates side conditions using a mutable reference.

    Implementation notes:

    - This could be done with a writer monad instead, but would be much more verbose.
    - This is unlike Rocq's rewriting using evars, where all occurrences subject to one evar
      instantiation are rewritten. The consequence is that a fixed number of subgoals is produced
      from the side conditions. In contarst, our scheme produces a number of side
      conditions/subgoals depending on the number of occurrences rewritten. This is because the
      instantiations are only discovered during traversal. *)
let rec pre_rewrite rewriter rule target =
  let open Monad in
  try
    pure (rewriter rule target)
  with Rewrite_failure _ ->
    match target with
    | Var _ | Symbol _ | Unit | True | False | Int _ | Nil | Emp -> pure target
    | Fun b -> Tm.fun_ <$> pre_rewrite_mbinder rewriter rule b
    | Apply (f, t) -> lift2 Tm.apply (pre_rewrite rewriter rule f) (pre_rewrite_list rewriter rule t)
    | Tuple ts -> Tm.tuple <$> pre_rewrite_list rewriter rule ts
    | Binop (op, t1, t2) -> lift2 (Tm.binop op) (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | Unop (op, t) -> Tm.unop op <$> pre_rewrite rewriter rule t
    | Conj (t1, t2) -> lift2 Tm.conj (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | Disj (t1, t2) -> lift2 Tm.disj (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | Implies (t1, t2) -> lift2 Tm.implies (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | Wand (t1, t2) -> lift2 Tm.wand (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | Subsumes (t1, t2) -> lift2 Tm.subsumes (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | PointsTo (t1, t2) -> lift2 Tm.pointsto (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | SepConj (t1, t2) -> lift2 Tm.sepconj (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | Requires t -> Tm.requires <$> pre_rewrite rewriter rule t
    | Ensures t -> Tm.ensures <$> pre_rewrite rewriter rule t
    | Sequence (t1, t2) -> lift2 Tm.sequence (pre_rewrite rewriter rule t1) (pre_rewrite rewriter rule t2)
    | Bind (t, b) -> lift2 Tm.bind (pre_rewrite rewriter rule t) (pre_rewrite_binder rewriter rule b)
    | Forall b -> Tm.forall <$> pre_rewrite_mbinder rewriter rule b
    | Exists b -> Tm.exists <$> pre_rewrite_mbinder rewriter rule b
    | Shift b -> Tm.shift <$> pre_rewrite_binder rewriter rule b
    | Reset t -> Tm.reset <$> pre_rewrite rewriter rule t

and pre_rewrite_list rewriter rule target =
  let open Monad in
  match target with
  | [] -> pure []
  | t :: ts ->
      let* t = pre_rewrite rewriter rule t in
      let* ts = pre_rewrite_list rewriter rule ts in
      pure (t :: ts)

and pre_rewrite_binder rewriter rule target =
  let open Monad in
  let x, target = unbind target in
  generalize x <$> pre_rewrite rewriter rule target

and pre_rewrite_mbinder rewriter rule target =
  let open Monad in
  let xs, target = unmbind target in
  mgeneralize xs <$> pre_rewrite rewriter rule target

let rewrite rule target =
  let open Monad in
  let* target = pre_rewrite rewrite_exact rule target in
  pure target

let rewrite_assoc rule target =
  let open Monad in
  let* target = pre_rewrite rewrite_exact_assoc rule target in
  pure target
