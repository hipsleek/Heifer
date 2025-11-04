

(* Complications:

  - In the formalization, all closures must be placed in a separate store, unlike here,
  where we can directly embed it into the specification as a TLambda.

  - All primitive functions cannot directly be lifted to coq-level functions. to "assert"
  a value is of a given type, we need to either add a (fex (fun typed_val : T => ens_ \[untyped_val = vconstructor typed_val] ;; ...))
  -like condition to the spec, or admit lemmas that state exactly this. and this isn't taking into account
  the fact that we won't always have types before smt!!!
  
  - i feel like it is safe to couple this to work specifically with coq since YAGNI
  support for anything else?

  *)

open Hipcore_typed.Typedhip

type 'a proof_log

type 'a partial_proof_log

val empty_partial_log : 'a partial_proof_log

val proof_step : 'a -> 'a proof_log

val append : 'a partial_proof_log -> 'a proof_log -> 'a partial_proof_log

val open_subproof : 'a partial_proof_log -> 'a partial_proof_log

val close_subproof : 'a partial_proof_log -> 'a partial_proof_log

val finalize_proof_log : 'a partial_proof_log -> 'a proof_log

type constr

val string_of_constr : constr -> string

(* this prototype version deliberately excludes calling functions from the context *)
val statement_of_entailment : staged_spec -> staged_spec -> constr
