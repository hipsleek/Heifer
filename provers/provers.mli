open Hiptypes

val askZ3 : pi -> bool
val valid : pi -> bool
val entails_exists : pi -> string list -> pi -> bool
val handle : (unit -> unit) -> unit
