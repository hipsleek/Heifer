open Hipcore
open Hiptypes

val askZ3 : typ_env -> pi -> bool
val valid : pi -> bool
val entails_exists : typ_env -> pi -> string list -> pi -> bool
val handle : (unit -> unit) -> unit
