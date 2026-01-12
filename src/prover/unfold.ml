(** Implementation of the [unfold] tactic.

    To unfold a symbol, we traverse a specification, lookup the definition of
    the symbol, and do substitution. *)

open Bindlib
open Core.Syntax

let rec unfold sym def s =
  match s with
  | Requires p -> Requires p
  | Ensures p -> Ensures p
  | Sequence (s1, s2) -> Sequence (unfold sym def s1, unfold sym def s2)
  | Bind (s, b) -> Bind (unfold sym def s, unfold_binder sym def b)
  | Apply (Symbol sym', ts) when sym = sym' -> msubst def (Array.of_list ts)
  | Apply (t1, t2) -> Apply (t1, t2)
  | Disj (s1, s2) -> Disj (unfold sym def s1, unfold sym def s2)
  | Forall b -> Forall (unfold_mbinder sym def b)
  | Exists b -> Exists (unfold_mbinder sym def b)
  | Shift b -> Shift (unfold_binder sym def b)
  | Reset s -> Reset (unfold sym def s)
  | Unit | True | False | Nil | Emp | Var _ | Symbol _ | Int _ | Fun _ | Tuple _
  | Binop (_, _, _)
  | Unop (_, _)
  | Conj (_, _)
  | Implies (_, _)
  | Subsumes (_, _)
  | PointsTo (_, _)
  | SepConj (_, _) ->
    assert false

and unfold_binder sym def b =
  let x, s = unbind b in
  unbox (bind_var x (box_staged_spec (unfold sym def s)))

and unfold_mbinder sym def b =
  let x, s = unmbind b in
  unbox (bind_mvar x (box_staged_spec (unfold sym def s)))
