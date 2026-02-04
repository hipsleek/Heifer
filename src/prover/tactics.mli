open Tactic
open Core.Syntax

val admit : unit t
val ex_falso : unit t
val forward : string -> unit t
val specialize : string -> string list -> unit t
val have : name:string -> string -> unit t
val case : name:string -> string -> unit t
val goal_is : string -> unit t
val qed : unit t
val refl : Pctx.t t
val rewrite : [ `Ltr | `Rtl ] -> term -> unit t
val induction : ?vars:string list -> name:string -> [ `Int of int | `List ] -> string -> unit t
val prove : unit t

module Pure : sig
  val ens_intro : unit t
  val ens_pure_elim : string -> unit t
  val req_pure_intro : string -> unit t
  val impl_intro : string -> unit t
  val intro_pure : string -> unit t
  val pure_solver : unit t
  val req_pure_elim : unit t
  val ens_pure_intro : unit t
  val elim_pure : unit t
  val revert_pure : string -> unit t
  val clear_pure : string -> unit t
end

module Simpl : sig
  val simpl_beta : unit t
  val simpl : unit t
  val shift_reset_reduce : unit t
  val prenex_assoc : unit t
end

val revert : string -> unit t
val forall_intro : unit t
val forall_elim : string list -> unit t
val exists_intro : string list -> unit t
val exists_elim : unit t

module Conj : sig
  val conj_elim : (term * term -> term) -> unit t
  val conj_elim_l : unit t
  val conj_elim_r : unit t
  val conj_intro : unit t
end

module Disj : sig
  val disj_elim : unit t
  val left : unit t
  val right : unit t
end

module Heaps : sig
  val ens_heap_elim : unit t
  val req_heap_intro : unit t
  val intro_heap : unit t
  val intros_heap : unit t
  val heap_solver : unit t
  val req_heap_elim : unit t
  val ens_heap_intro : unit t
  val elim_heap : unit t
  val revert_heap : unit t
end

module Unmix : sig
  val unmix : unit t
end

(** Tactic scripting *)

val parse_term : string -> term t
val is_pure : term -> bool
val is_heap : term -> bool
val uncons_ens : term -> (term * term) t
val uncons_req : term -> (term * term) t
val get_subsumption : (term * term) t
val put_subsumption : term -> term -> unit t
val put_lhs : term -> unit t
val put_rhs : term -> unit t
val get_lhs : term t
val get_rhs : term t
val unwrap : 'a option -> string -> 'a t
val guard : bool -> string -> unit t
val all_goals : 'a t -> Pctx.t list -> (unit * Pctx.t list, string) result
val semicolon1 : 'a t -> 'b t -> unit t
val semicolon : 'a t -> 'b t -> Pctx.t list -> (Pctx.t list, string) result
val push_pure_goals : term list -> unit t
val invoke_why3 : term -> [> `Invalid | `Unknown of string | `Valid ] t
val fresh : string t
