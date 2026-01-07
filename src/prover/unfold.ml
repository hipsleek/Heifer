(** Implementation of the [unfold] tactic.

    To unfold a symbol, we traverse a specification, lookup the definition
    of the symbol, and do substitution. *)

open Bindlib
open Core.Syntax

let rec unfold_aux sym def s =
  match s with
  | Return t -> Return t
  | Requires p -> Requires p
  | Ensures p -> Ensures p
  | Sequence (s1, s2) -> Sequence (unfold_aux sym def s1, unfold_aux sym def s2)
  | Bind (s, b) -> Bind (unfold_aux sym def s, unfold_binder_aux sym def b)
  | Apply (TSymbol sym', t) when sym = sym' -> subst def t
  | Apply (t1, t2) -> Apply (t1, t2)
  | Disjunct (s1, s2) -> Disjunct (unfold_aux sym def s1, unfold_aux sym def s2)
  | Forall b -> Forall (unfold_binder_aux sym def b)
  | Exists b -> Exists (unfold_binder_aux sym def b)
  | Shift b -> Shift (unfold_binder_aux sym def b)
  | Reset s -> Reset (unfold_aux sym def s)
  | Dollar _ -> failwith "todo"
and unfold_binder_aux sym def b =
  let x, s = unbind b in
  unbox (bind_var x (box_staged_spec (unfold_aux sym def s)))

let unfold sym defs s =
  match SymMap.find_opt sym defs with
  | None -> s
  | Some def -> unfold_aux sym def s
