open Hiptypes

val subst_free_vars : (string * term) list -> staged_spec -> staged_spec

val free_vars : staged_spec -> SSet.t
val free_vars_term : term -> SSet.t
val free_vars_pure : pi -> SSet.t
val free_vars_heap : kappa -> SSet.t
