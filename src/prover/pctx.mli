open Core.Syntax
open Core

type t = {
  rename_ctxt : Rename.ctxt;
  constants : term Bindlib.var Map.Make(String).t;
  assumptions : term Map.Make(String).t;
  heap_assumptions : term list;
  goal : term;
}

val create : goal:term -> t
val pp : Format.formatter -> t -> unit
