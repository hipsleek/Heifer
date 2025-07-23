
type prover_result =
  | Valid
  | Invalid
  | Unknown of string

type quantified_var =
  | QExists of string
  | QForAll of string

val var_of_quantifier : quantified_var -> string

exception Prover_error of string

val string_of_prover_result : prover_result -> string
