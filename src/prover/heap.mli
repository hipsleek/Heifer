
open Core.Syntax

type heaplet
type heap

val hprop_to_heap : hprop -> heap

val heap_to_hprop : heap -> hprop

val hprop_list_to_heap : hprop list -> heap

val heap_to_hprop_list : heap -> hprop list

(** Destruct a heap proposition into atomic heap propositions of the form
    [t1 -> t2]. [Emp] is eliminated.

    Raise [Invalid_argument] if argument is not a heap proposition *)
val deep_destruct_sepconj : hprop -> hprop list

(* TODO: improve the interface of this module! *)

val match_heap : heap -> heap -> heap * heap * heap * prop list

val biab : hprop -> hprop -> hprop * hprop * prop

val biab_list : hprop list -> hprop list -> hprop list * hprop list * prop list

val xpure : hprop -> prop
