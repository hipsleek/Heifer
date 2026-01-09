(** Implementation of the [unfold] tactic.

    To unfold a symbol, we traverse a specification, lookup the definition
    of the symbol, and do substitution. *)

open Bindlib
open Core.Syntax

let rec unfold sym def s =
  match s with
  | Return t -> Return t
  | Requires p -> Requires p
  | Ensures p -> Ensures p
  | Sequence (s1, s2) -> Sequence (unfold sym def s1, unfold sym def s2)
  | Bind (s, b) -> Bind (unfold sym def s, unfold_binder sym def b)
  | Apply (TSymbol sym', ts) when sym = sym' -> msubst def (Array.of_list ts)
  | Apply (t1, t2) -> Apply (t1, t2)
  | Disjunct (s1, s2) -> Disjunct (unfold sym def s1, unfold sym def s2)
  | Forall b -> Forall (unfold_mbinder sym def b)
  | Exists b -> Exists (unfold_mbinder sym def b)
  | Shift b -> Shift (unfold_binder sym def b)
  | Reset s -> Reset (unfold sym def s)
  | Dollar _ -> failwith "todo"

and unfold_binder sym def b =
  let x, s = unbind b in
  unbox (bind_var x (box_staged_spec (unfold sym def s)))

and unfold_mbinder sym def b =
  let x, s = unmbind b in
  unbox (bind_mvar x (box_staged_spec (unfold sym def s)))
