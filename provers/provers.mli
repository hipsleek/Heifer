open Hipcore
open Hiptypes
open Typedhip

(** check if [p1 => ex vs. p2] is valid.
    background definitions are given using global state. *)
val entails_exists : typ_env -> pi -> binder list -> pi -> bool

val handle : (unit -> unit) -> unit
