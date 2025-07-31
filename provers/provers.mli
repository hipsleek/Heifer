open Hipcore_typed.Typedhip
open Hipcore.Types

open Provers_common

(** check if [p1 => ex vs. p2] is valid.
    background definitions are given using global state. *)
val entails_exists : typ_env -> pi -> string list -> pi -> prover_result

val handle : (unit -> unit) -> unit
