(** Implementation of the [unfold] tactic. *)

open Bindlib
open Core.Syntax
open Core.Syntax_util

let rec unfold sym def t =
  match t with
  | Unit | True | False | Nil | Emp | Var _ | Symbol _ | Int _ | ONone -> t
  | OSome t -> OSome (unfold sym def t)
  | Requires t -> Requires (unfold sym def t)
  | Ensures t -> Ensures (unfold sym def t)
  | Sequence (t1, t2) -> Sequence (unfold sym def t1, unfold sym def t2)
  | Bind (t, b) -> Bind (unfold sym def t, unfold_binder sym def b)
  | Apply (Symbol sym', ts) when sym = sym' -> msubst def (Array.of_list ts)
  | Apply (t, ts) -> Apply (unfold sym def t, unfold_list sym def ts)
  | Disj (t1, t2) -> Disj (unfold sym def t1, unfold sym def t2)
  | Forall b -> Forall (unfold_mbinder sym def b)
  | Exists b -> Exists (unfold_mbinder sym def b)
  | Shift b -> Shift (unfold_binder sym def b)
  | Reset t -> Reset (unfold sym def t)
  | Fun b -> Fun (unfold_mbinder sym def b)
  | Tuple ts -> Tuple (unfold_list sym def ts)
  | Binop (op, t1, t2) -> Binop (op, unfold sym def t1, unfold sym def t2)
  | Unop (op, t) -> Unop (op, unfold sym def t)
  | Conj (t1, t2) -> Conj (unfold sym def t1, unfold sym def t2)
  | Implies (t1, t2) -> Implies (unfold sym def t1, unfold sym def t2)
  | Wand (t1, t2) -> Wand (unfold sym def t1, unfold sym def t2)
  | Subsumes (t1, t2) -> Subsumes (unfold sym def t1, unfold sym def t2)
  | PointsTo (t1, t2) -> PointsTo (unfold sym def t1, unfold sym def t2)
  | SepConj (t1, t2) -> SepConj (unfold sym def t1, unfold sym def t2)

and unfold_list sym def ts = List.map (unfold sym def) ts

and unfold_binder sym def b =
  let x, t = unbind b in
  generalize x (unfold sym def t)

and unfold_mbinder sym def b =
  let xs, t = unmbind b in
  mgeneralize xs (unfold sym def t)
