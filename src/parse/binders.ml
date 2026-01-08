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

let get x =
  match Hashtbl.find_opt unbound_vars x with None -> new_tvar x | Some y -> y
