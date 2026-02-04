open Syntax

val is_pure_term : term -> bool
val could_be_prop : term -> bool
val is_hprop : term -> bool
val check_sort : term -> (sort, string) result
