open Types

val askZ3 : pi -> bool
val entails_exists : pi -> string list -> pi -> bool
val handle : (unit -> unit) -> unit
val normalPure : pi -> pi
