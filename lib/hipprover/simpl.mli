open Hipcore
open Hiptypes

val simplify_term : term -> term

val simplify_pure : pi -> pi

val simplify_kappa : kappa -> kappa

val simplify_spec : staged_spec -> staged_spec
