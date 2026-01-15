open Core.Syntax

val prove :
  ?show_goal:bool -> term -> [> `Invalid | `Unknown of string | `Valid ]

val is_translatable : term -> bool
