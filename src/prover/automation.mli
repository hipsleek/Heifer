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
  | Intro_pure
  | Rewrite of term * cert list * cert
  | Disj_elim of cert * cert

and cert = cert_tac list

val pp_cert_tac : cert_tac Fmt.t
val pp_cert : Format.formatter -> cert -> unit
val solve_cert : cert t
