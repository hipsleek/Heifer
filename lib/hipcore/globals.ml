open Common
open Typedhip

let using_pure_fns = ref false

type t = {
  mutable pure_fns : pure_fn_def SMap.t;
  mutable pure_fn_types : pure_fn_type_def SMap.t;
  mutable type_decls: type_decl SMap.t
}

let create_empty () = { pure_fns = SMap.empty; pure_fn_types = SMap.empty; type_decls = SMap.empty}
let global_environment : t = 
  let open Types in
  let empty = create_empty () in
  { empty with
    type_decls = empty.type_decls |> SMap.add "list" {
      typ_name = "list"; 
      typ_params = [TVar "a"];
      typ_kind = Tdecl_inductive [("::", [TVar "a"; TConstr ("list", [TVar "a"])]); ("[]", [])]
    }
  }

(* we don't want to thread the type definitions through every single normalization call, since normalization invokes the prover. this part of the state grows monotonically, so it should be harmless... *)
let define_pure_fn name typ =
  using_pure_fns := true;
  global_environment.pure_fns <- SMap.add name typ global_environment.pure_fns

let is_pure_fn_defined f = SMap.mem f global_environment.pure_fns
let pure_fn f = SMap.find f global_environment.pure_fns
let pure_fns () = SMap.bindings global_environment.pure_fns

let decl_of_type_name name = SMap.find name global_environment.type_decls

module Timing = struct
  let overall_all = ref 0.
  let overall = ref 0.
  let provers_all = ref 0.
  let forward = ref 0.
  let entail = ref 0.
  let norm = ref 0.
  let z3 = ref 0.
  let why3 = ref 0.
  let z3_all = ref 0.
  let why3_all = ref 0.

  let update_totals () =
    provers_all := !provers_all +. !z3 +. !why3;
    z3_all := !z3_all +. !z3;
    why3_all := !why3_all +. !why3;
    z3 := 0.;
    why3 := 0.;
    forward := 0.;
    entail := 0.;
    norm := 0.;
    overall := 0.

  (* let time_sec () = Unix.gettimeofday () *)
  let time_sec () = Sys.time ()
  let milliseconds_since start = (time_sec () -. start) *. 1000.0

  let time what f =
    let start = time_sec () in
    let@ _ = protected f in
    what := !what +. milliseconds_since start
end
