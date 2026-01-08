open Syntax

(** A symbol table is like a namespace, which is a map between symbols and their
    correponding definitions. *)
type symbol_table = def SymMap.t

let empty_table = SymMap.empty

let add_decl sym def table =
  (* if the symbol is already in the symbol table, throw an error *)
  if SymMap.mem sym table then raise (Failure "symbol is already declared");
  SymMap.add sym def table

(* TODO: add a sample decl for foldr *)
