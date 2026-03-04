open Core.Syntax
open Tactic

(** UNSTABLE *)

(** Some automation tactics *)

val repeat : unit t -> unit t
val focus : 'a t -> 'a t
val dbg_state : unit t

(** Simple automation *)

val simple : ?lemmas:(string * term) list -> ?depth:int -> unit t
val dbg_simple : ?lemmas:(string * term) list -> ?depth:int -> unit t

(** Certifying automation *)

type cert =
  | Smt of term
  | Forall_intro of cert
  | Exists_elim of cert
  | Forall_elim of term list * cert
  | Exists_intro of term list * cert
  | Intro_pure of string * cert
  | Elim_pure of cert
  | Intro_heap of cert
  | Elim_heap of cert
  | Rewrite of string * term * cert list * cert
  | Disj_elim of cert * cert
  | Left of cert
  | Right of cert
  | Refl
  | Ex_falso

val pp_cert : Format.formatter -> cert -> unit [@@toplevel_printer]
val solve_cert : ?lemmas:(string * term) list -> ?depth:int -> cert t
