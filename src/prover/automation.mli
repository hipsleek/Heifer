open Core.Syntax
open Tactic

(** UNSTABLE *)

val fresh : string t
val repeat : unit t -> unit t
val try_ : ('a -> (unit * 'a, 'b) result) -> 'a -> (unit * 'a, 'c) result
val maybe_prove_pure : unit t
val intro_pure : unit t
val debug : string -> 'a t -> 'a t
val dbg : string -> unit t
val ( >> ) : unit t -> 'a t -> 'a t
val ( >>> ) : 'a t -> unit t -> 'a t

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
val focus_and_solve_with : 'a t -> 'a t
val focus : Pctx.t list t
val init : 'a list -> 'a list * 'a
val possible_rewrites2 : (unit -> cert t) -> cert_tac t list t
val disj_elim : (unit -> cert t) -> cert_tac t
val solve_cert : cert t
val possible_rewrites : unit t list t
val simple : unit t
