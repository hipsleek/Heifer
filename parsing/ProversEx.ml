open Hipcore
open Hiptypes
open Infer_types

(* we need this module because https://dune.readthedocs.io/en/stable/variants.html#:~:text=It%E2%80%99s%20not%20possible%20for%20implementations%20to%20introduce%20new%20public%20modules *)


let is_valid pi1 pi2 =
  let env =
    let env = create_abs_env () in
    let env = infer_types_pi env pi1 in
    let env = infer_types_pi env pi2 in
    concrete_type_env env
  in
  Provers.entails_exists env pi1 [] pi2
