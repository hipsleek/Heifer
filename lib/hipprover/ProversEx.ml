open Hipcore
open Hiptypes
open Infer_types
open Pretty
open Debug

(* we need this module because https://dune.readthedocs.io/en/stable/variants.html#:~:text=It%E2%80%99s%20not%20possible%20for%20implementations%20to%20introduce%20new%20public%20modules *)


let is_valid pi1 ?(ex=[]) pi2 =
  let env = create_abs_env () in
  let pi1, env = infer_untyped_pi ~env pi1 in
  let pi2, env = infer_untyped_pi ~env pi2 in
  let concrete_env = concrete_type_env env
  in
  let@ _ =
    Debug.span (fun r ->
        debug ~at:4
          ~title:"is_valid"
          "%s => %s\n%s" (Pretty_typed.string_of_pi pi1) (Pretty_typed.string_of_pi pi2)
          (string_of_result string_of_res r))
  in
  let typed_ex = List.map (fun v -> (v, SMap.find_opt v concrete_env |> Option.value ~default:(Typedhip.new_type_var ()))) ex in
  Provers.entails_exists concrete_env pi1 typed_ex pi2
