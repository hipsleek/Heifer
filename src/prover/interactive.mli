open Core.Syntax

module State : sig
  val start_proof : string -> unit
  val reset_proof_state : unit -> unit
  val push_proof_state : unit -> unit
  val pop_proof_state : unit -> unit
  val declare : string -> unit
  val axiom : name:string -> string -> unit
  val lemma : name:string -> string -> unit
  val qed : unit -> unit
end

val have : name:string -> string -> unit
val case : name:string -> string -> unit
val goal_is : string -> unit
val specialize : string -> string list -> unit
val forward : string -> unit
val refl : unit -> unit
val req_heap_intro : unit -> unit
val ens_heap_elim : unit -> unit
val req_heap_elim : unit -> unit
val ens_heap_intro : unit -> unit
val req_pure_intro : string -> unit
val req_pure_elim : unit -> unit
val ens_pure_intro : unit -> unit
val ens_pure_elim : string -> unit
val intro_pure : string -> unit
val elim_pure : unit -> unit
val intro_heap : unit -> unit
val intros_heap : unit -> unit
val elim_heap : unit -> unit
val revert : string -> unit
val revert_pure : string -> unit
val clear_pure : string -> unit
val pure_solver : unit -> unit
val revert_heap : unit -> unit
val heap_solver : unit -> unit
val forall_intro : unit -> unit
val forall_elim : string list -> unit
val exists_intro : string list -> unit
val exists_elim : unit -> unit
val conj_elim_l : unit -> unit
val conj_elim_r : unit -> unit
val disj_elim : unit -> unit
val left : unit -> unit
val right : unit -> unit
val simpl_beta : unit -> unit
val simpl : unit -> unit
val shift_reset_reduce : unit -> unit
val unmix : unit -> unit
val ex_falso : unit -> unit
val prove : unit -> unit
val admit : unit -> unit
val prove_s : string -> [> `Invalid | `Unknown of string | `Valid ]
val simple : unit -> unit
val simple2 : unit -> (Automation.cert * Pstate.t, string) result
val unfold : string -> unit
val induction : ?vars:string list -> name:string -> [ `Int of int | `List ] -> string -> unit
val interactive_get_assumption : string -> term Tactic.t
val rewrite : ?direction:[ `Ltr | `Rtl ] -> string -> unit
