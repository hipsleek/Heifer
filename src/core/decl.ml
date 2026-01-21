open Syntax

(** A symbol table is like a namespace, which is a map between symbols and their
    correponding definitions. *)
type symbol_table = def SymMap.t

let empty_table = SymMap.empty

(** Add a new declaration to a symbol table. *)
let add_decl sym def (table : symbol_table) : symbol_table =
  SymMap.add sym def table
