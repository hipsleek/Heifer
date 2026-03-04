open Core.Syntax
open Bindlib
open Util.Strings

(** When parsing input into an AST that uses Bindlib, variables and their
    binders have to use physically equal vars (created with e.g. [new_tvar]).

    This module provides a stateful symbol table (mapping string names
    encountered to Bindlib [var]s) for doing this.

    - When a binder is encountered, a [new_tvar] is created.
    - The [var] is used when a variable is parsed.
    - On the way up past the binder, it is removed.
    - The [add]/[remove] behaviour of [Hashtbl]s handles shadowing. *)
type t

val init : term var SMap.t -> unit
val create : string -> unit
val remove : string -> term var
val remove_all : string list -> term mvar

(** Resolve an identifier when parsing:
    - If the identifier is bound, then it's a variable.
    - Otherwise, we assume that it is a symbol.

    In the future, we may maintain a symbol table for the parser, if we have
    multiple kind of symbols. *)
val resolve_identifier : string -> term
