
open Hiptypes

let using_pure_fns = ref false

type t = {
  mutable pure_fns : pure_fn_def SMap.t;
  mutable pure_fn_types : pure_fn_type_def SMap.t;
}

let create () = {
  pure_fns = SMap.empty;
  pure_fn_types = SMap.empty;
}
let global_environment : t = create ()

(* we don't want to thread the type definitions through every single normalization call, since normalization invokes the prover. this part of the state grows monotonically, so it should be harmless... *)
let define_pure_fn name typ =
  using_pure_fns := true;
  global_environment.pure_fns <-
    SMap.add name typ global_environment.pure_fns

let is_pure_fn_defined f =
  SMap.mem f global_environment.pure_fns

let pure_fn f =
  SMap.find f global_environment.pure_fns

let pure_fns () =
  SMap.bindings global_environment.pure_fns