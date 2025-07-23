open Hipcore_typed.Typedhip

type prover_result =
  | Valid
  | Invalid
  | Unknown of string

type quantified_var =
  | QExists of binder
  | QForAll of binder

let binder_of_quantifier v =
  match v with
  | QExists s | QForAll s -> s

exception Prover_error of string

let string_of_prover_result = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown s -> "unknown (" ^ s ^ ")"
 
let () =
  Printexc.register_printer begin function
    | Prover_error s -> Some (Printf.sprintf "Prover_error(%s)" s)
    | _ -> None
  end
