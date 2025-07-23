open Hipcore_typed.Typedhip

open Provers_common

(** check if [p1 => vs. p2] is valid.
    background definitions are given using global state. 
    vs is ordered such that variables with outermost scope come first. *)
val entails_exists : pi -> quantified_var list -> pi -> prover_result

val handle : (unit -> unit) -> unit
