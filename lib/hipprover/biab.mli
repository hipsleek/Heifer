open Hipcore
open Hiptypes

type biab_ctx = {
  equalities: pi list;
}

val emp_biab_ctx : biab_ctx

(** [solve ctx h1 h2] solves the biabduction problem {m A * H_1 \vdash H_2 * F}.
    Returns {m H_1}, {m A}, {m F}, and extra equalities required to make {m H_1 = H_2}.
*)
val solve : biab_ctx -> kappa -> kappa -> kappa list * kappa list * kappa list * biab_ctx
