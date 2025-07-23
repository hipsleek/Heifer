open Hipcore_typed.Typedhip

type prover_result =
  | Valid
  | Invalid
  | Unknown of string

type quantified_var =
  | QExists of binder
  | QForAll of binder

val binder_of_quantifier : quantified_var -> binder

exception Prover_error of string

val string_of_prover_result : prover_result -> string
