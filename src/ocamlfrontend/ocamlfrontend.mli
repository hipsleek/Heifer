open Core.Syntax

(** Generates staged logic defintions and proof obligations from OCaml source *)
val get_definitions_and_obligations : string -> (string * def) list * Obligations.t
