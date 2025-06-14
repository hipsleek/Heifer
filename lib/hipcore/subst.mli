open Hiptypes

val subst_free_vars : (string * term) list -> staged_spec -> staged_spec

val free_vars : staged_spec -> Common.SSet.t
