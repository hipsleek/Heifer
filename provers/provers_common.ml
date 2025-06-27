
type prover_result =
  | Valid
  | Invalid
  | Unknown of string

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
