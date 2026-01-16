open Core.Syntax
open Util.Strings
open Bindlib

type proof_context = {
  rename_ctxt : Bindlib.ctxt;
  constants : term var SMap.t;
  assumptions : term SMap.t;
  heap_assumptions : term list; (* TODO: add names *)
  goal : term;
}

let create ~goal = {
  rename_ctxt = Bindlib.empty_ctxt;
  constants = SMap.empty;
  assumptions = SMap.empty;
  heap_assumptions = [];
  goal;
}
