
open Core.Syntax

type heap

val hprop_to_heap : hprop -> heap

val heap_to_hprop : heap -> hprop

val deep_destruct_sepconj : hprop -> hprop list

(** Given two heap propositions, return a 4-tuple containing, in order:
    - The common heap.
    - The left-exclusive heap.
    - The right-exclusive heap.
    - Equalities to be satisfied. *)
val biab_aux : hprop -> hprop -> heap * heap * heap * term list

val biab : hprop -> hprop -> hprop * hprop

val xpure : hprop -> prop
