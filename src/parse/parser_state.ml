open Core.Syntax
open Bindlib
open Util.Strings

type t = (string, term var) Hashtbl.t

let unbound_vars : t = Hashtbl.create 10

let init m =
  Hashtbl.clear unbound_vars;
  Hashtbl.add_seq unbound_vars (SMap.to_seq m)

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

let resolve_identifier x =
  match Hashtbl.find_opt unbound_vars x with
  | None -> Symbol { sym_name = x }
  | Some v -> Var v
