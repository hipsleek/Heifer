open Core.Syntax

val prove :
  ?show_goal:bool -> term -> [> `Invalid | `Unknown of string | `Valid ]

val is_translatable : term -> bool
val get_smt_time : unit -> float
val reset_statistics : unit -> unit
