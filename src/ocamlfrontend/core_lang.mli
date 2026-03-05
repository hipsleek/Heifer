
type pattern =
  | PVar of string
  | PConstr of string * pattern list
  | PAny  (** [_] *)
  | PInt of int

(** OCaml programs *)
type expr =
  | Var of string
  | Int of int
  | Fun of string list * expr
  | Apply of expr * expr list
  | Let of string * expr * expr
  | If of expr * expr * expr
  | Sequence of expr * expr
  | Shift of string * expr
  | Reset of expr
  | Perform of string * expr option
  | Resume of expr list
  | Match of expr * (pattern * expr) list
  | WithSpec of expr * string * string (* the :: operator, as an expr *)

(** Analogous to a compilation unit; all the structure we get from a source file *)
type verification_unit = {
  pure_functions : (string * expr) list;
  program_functions : (string * expr) list;
}

val dump_pattern : Format.formatter -> pattern -> unit
val dump_term : Format.formatter -> expr -> unit
