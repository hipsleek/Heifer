
type prover_result =
  | Valid
  | Invalid
  | Unknown of string

exception Prover_error of string

val string_of_prover_result : prover_result -> string
