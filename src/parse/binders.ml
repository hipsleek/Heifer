
open Core.Syntax
open Bindlib

(** When parsing input into an AST that uses Bindlib, variables and their binders
  have to use physically equal vars (created with e.g. new_tvar).

  This module provides a stateful data structure for doing this. It is
  conceptually a symbol table mapping (string) names encountered to Bindlib vars.

  To handle shadowing, it is generalised to a stack of symbol tables, where each
  item on the stack models a scope.

  - When a binder is encountered, a new scope is pushed.
  - When a variable is encountered, it either creates or reuses a var of a given name in the topmost scope.
  - When ascending past a binder, the var is looked up before the scope is popped. *)

let unbound_vars : (string * term var) list list ref = ref [[]]

let reset_state () =
  unbound_vars := [[]]

let push_scope () =
  unbound_vars := [] :: !unbound_vars

let lookup_or_fresh x =
  match !unbound_vars with
  | [] -> assert false
  | h :: t ->
    match List.assoc_opt x h with
    | Some y -> y
    | None ->
      let y = new_tvar x in
      unbound_vars := ((x, y) :: h) :: t;
      y

let bind_variable x =
  match !unbound_vars with
  | [] -> assert false
  | h :: t ->
    let res =
      match List.assoc_opt x h with
      | None -> new_tvar x
      | Some y -> y
    in
    unbound_vars := t; (* pop scope *)
    res