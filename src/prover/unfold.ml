(** Implementation of the [unfold] tactic.
    
    To unfold a symbol, we traverse a specification, lookup the definition
    of the symbol, and do substitution. *)

open Core.Syntax
let unfold (sym : symbol) (s : staged_spec) : staged_spec =
  failwith "unfold: todo"
