open Core.Syntax

val prove : term -> [> `Invalid | `Unknown of string | `Valid ]
val is_translatable : term -> bool
