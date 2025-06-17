open Hipcore
open Hiptypes

val simplify_term : term -> term

val simplify_pure : pi -> pi

val simplify_kappa : kappa -> kappa

val simplify_spec : staged_spec -> staged_spec

(** [is_contradiction_kappa h] checks whether {m h} is a contradicting heap formula.
    A heap formula is contradicting, if there is a location {m x} and we have both
    {m x -> a * x -> b} for some term {m a} and {m b}.
 *)
val is_contradiction_kappa : kappa -> bool

(** [is_contradiction_pure p] checks whether {m p} is a contradicting pure formula.
  *)
val is_contradiction_pure : pi -> bool
