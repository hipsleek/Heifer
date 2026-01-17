open Core.Syntax
open Bindlib

(** When parsing input into an AST that uses Bindlib, variables and their
    binders have to use physically equal vars (created with e.g. [new_tvar]).

    This module provides a stateful symbol table (mapping string names
    encountered to Bindlib [var]s) for doing this.

    - When a binder is encountered, a [new_tvar] is created.
    - The [var] is used when a variable is parsed.
    - On the way up past the binder, it is removed.
    - The [add]/[remove] behaviour of [Hashtbl]s handles shadowing. *)

let unbound_vars : (string, term var) Hashtbl.t = Hashtbl.create 10
let reset_state () = Hashtbl.clear unbound_vars
let create x = Hashtbl.add unbound_vars x (new_tvar x)

let remove x =
  let r =
    match Hashtbl.find_opt unbound_vars x with
    | None -> new_tvar x
    | Some y -> y
  in
  Hashtbl.remove unbound_vars x;
  r

let remove_all xs = List.map remove xs |> Array.of_list
let get = Hashtbl.find unbound_vars
let get_opt = Hashtbl.find_opt unbound_vars

(** Resolve an identifier when parsing:
    - If the identifier is bound, then it's a variable.
    - Otherwise, we assume that it is a symbol.

    In the future, we may maintain a symbol table for the parser, if we have
    multiple kind of symbols. *)
let resolve_identifier x =
  match get_opt x with
  | None -> Symbol { sym_name = x }
  | Some v -> Var v
