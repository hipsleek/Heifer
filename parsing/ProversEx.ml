open Hipcore
open Hiptypes
open Infer_types
open Pretty
open Debug

(* we need this module because https://dune.readthedocs.io/en/stable/variants.html#:~:text=It%E2%80%99s%20not%20possible%20for%20implementations%20to%20introduce%20new%20public%20modules *)


let is_valid ?(pure_fns=SMap.empty) pi1 pi2 =
  let env =
    let env = create_abs_env () in
    let env = infer_types_pi pure_fns env pi1 in
    let env = infer_types_pi pure_fns env pi2 in
    concrete_type_env env
  in
  let@ _ =
    Debug.span (fun r ->
        debug ~at:4
          ~title:"is_valid"
          "%s => %s\n%s" (string_of_pi pi1) (string_of_pi pi2)
          (string_of_result string_of_res r))
  in
  Provers.entails_exists ~pure_fns env pi1 [] pi2
