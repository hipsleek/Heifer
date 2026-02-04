open Core.Syntax
open Tactic

(** UNSTABLE *)

(** Some automation tactics *)

val repeat : unit t -> unit t
val or_rollback : unit t -> unit t
val focus_and_solve_with : 'a t -> 'a t

(** Simple automation *)

val simple : unit t

(** Certifying automation *)

type cert_tac =
  | Smt of term
  | Forall_intro
  | Exists_elim
  | Intro_pure of string
  | Rewrite of string * term * cert list * cert
  | Disj_elim of cert * cert
  | Left
  | Right

and cert = cert_tac list

val pp_cert_tac : cert_tac Fmt.t [@@toplevel_printer]
val pp_cert : Format.formatter -> cert -> unit [@@toplevel_printer]
val solve_cert : ?lemmas:(string * term) list -> cert t
