open Typedhip
open Common
open Types

let using_pure_fns = ref false

type t = {
  mutable pure_fns : pure_fn_def SMap.t;
  mutable pure_fn_types : pure_fn_type_def SMap.t;
  mutable type_declarations : type_declaration SMap.t
}

let create () = { pure_fns = SMap.empty; pure_fn_types = SMap.empty; type_declarations = SMap.empty }
let global_environment : t = 
  let empty = create () in
  {empty with
    type_declarations = empty.type_declarations |> SMap.add "list" {
      tdecl_name = "list"; 
      tdecl_params = [TVar "a"];
      tdecl_kind = Tdecl_inductive [("::", [TVar "a"; TConstr ("list", [TVar "a"])]); ("[]", [])]
    } |> SMap.add "ref" { (* not strictly needed; just a placeholder to let the frontend know that the 'a ref type constructor exists *)
      tdecl_name = "ref";
      tdecl_params  = [TVar "a"];
      tdecl_kind = Tdecl_record [{field_name = "contents"; field_type = TVar "a"}]
    }
  }

(* we don't want to thread the type definitions through every single normalization call, since normalization invokes the prover. this part of the state grows monotonically, so it should be harmless... *)
let define_pure_fn name typ =
  using_pure_fns := true;
  global_environment.pure_fns <- SMap.add name typ global_environment.pure_fns

let define_type tdecl =
  global_environment.type_declarations <- SMap.add tdecl.tdecl_name tdecl global_environment.type_declarations

let find_type_decl name = SMap.find name global_environment.type_declarations

(** Given a type constructor's name, return its type declaration, and
    the types of its arguments.

    Raises Not_found if no such constructor is found. *)
let type_constructor_decl name =
  let decls = SMap.bindings global_environment.type_declarations
  |> List.filter_map (fun (_, type_decl) -> Types.constructor_of_type_decl name type_decl |> Option.map (fun constr_decl -> (type_decl, constr_decl)))
  in
  if List.is_empty decls
  then failwith ("Could not find constructor " ^ name)
  else List.hd decls

let is_pure_fn_defined f = SMap.mem f global_environment.pure_fns
let pure_fn f = SMap.find f global_environment.pure_fns
let pure_fns () = SMap.bindings global_environment.pure_fns
let type_decls () = SMap.bindings global_environment.type_declarations

module Timing = struct
  let overall_all = ref 0.
  let provers_all = ref 0.
  let forward = ref 0.
  let entail = ref 0.
  let norm = ref 0.
  let z3 = ref 0.
  let why3 = ref 0.
  let z3_all = ref 0.
  let why3_all = ref 0.

  let update_totals () =
    overall_all := !overall_all +. !z3 +. !why3 +. !forward +. !entail +. !norm;
    provers_all := !provers_all +. !z3 +. !why3;
    z3_all := !z3_all +. !z3;
    why3_all := !why3_all +. !why3;
    z3 := 0.;
    why3 := 0.;
    forward := 0.;
    entail := 0.;
    norm := 0.

  (* let time_sec () = Unix.gettimeofday () *)
  let time_sec () = Sys.time ()
  let milliseconds_since start = (time_sec () -. start) *. 1000.0

  let time what f =
    let start = time_sec () in
    let@ _ = protected f in
    what := !what +. milliseconds_since start
end
