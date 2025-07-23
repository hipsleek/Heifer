open Hipcore
open Typedhip
open Types

open Provers_common

(** check if [p1 => vs. p2] is valid.
    background definitions are given using global state. 
    vs is ordered such that variables with outermost scope come first. *)
val entails_exists : typ_env -> pi -> quantified_var list -> pi -> prover_result

val handle : (unit -> unit) -> unit
