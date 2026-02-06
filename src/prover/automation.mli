open Core.Syntax
open Tactic

(** UNSTABLE *)

(** Some automation tactics *)

val repeat : unit t -> unit t
val focus_and_solve_with : 'a t -> 'a t

(** Simple automation *)

val simple : ?lemmas:(string * term) list -> unit t

(** Certifying automation *)

type cert_tac =
  | Smt of term
  | Forall_intro
  | Exists_elim
  | Forall_elim of term array
  | Exists_intro of term array
  | Intro_pure of string
  | Elim_pure
  | Intro_heap
  | Elim_heap
  | Rewrite of string * term * cert list * cert
  | Disj_elim of cert * cert
  | Left of cert
  | Right of cert
  | Refl
  | Ex_falso

and cert = cert_tac list

val pp_cert_tac : cert_tac Fmt.t [@@toplevel_printer]
val pp_cert : Format.formatter -> cert -> unit [@@toplevel_printer]
val solve_cert : ?lemmas:(string * term) list -> cert t
