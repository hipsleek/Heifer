
open Core.Syntax

(** [solve h1 h2] solves the biabduction problem {m A * H_1 \vdash H_2 * F}.
    Returns {m H_1}, {m A}, {m F}, and extra equalities required to make {m H_1 = H_2}.
*)
val solve : hprop -> hprop -> hprop list * hprop list * hprop list * prop list

val xpure : hprop -> prop
