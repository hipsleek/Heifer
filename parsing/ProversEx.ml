open Hipcore
open Hiptypes
open Infer_types

(* we need this module because https://dune.readthedocs.io/en/stable/variants.html#:~:text=It%E2%80%99s%20not%20possible%20for%20implementations%20to%20introduce%20new%20public%20modules *)

let entailConstrains pi1 pi2 =
  let env =
    let env = create_abs_env () in
    let env = infer_types_pi env pi1 in
    let env = infer_types_pi env pi2 in
    concrete_type_env env
  in
  let sat = not (Provers.askZ3 env (Not (Or (Not pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat
