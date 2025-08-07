(** Implementation of the State monad. *)

type ('a, 'state) state = 'state -> 'a * 'state

val return : 'a -> ('a, 'state) state
val bind : ('a, 'state) state -> ('a -> ('b, 'state) state) -> ('b, 'state) state
val (let*) : ('a, 'state) state -> ('a -> ('b, 'state) state) -> ('b, 'state) state

(** Retrieve the current state. *)
val get : ('state, 'state) state

(** Wrap a stateful computation such that the state is not modified at the end. *)
val scope : ('a, 'state) state -> ('a, 'state) state

(** Apply a function to the state. *)
val mutate : ('state -> 'state) -> (unit, 'state) state

(** Apply a pure computation to the value. *)
val map : ('a -> 'b) -> ('a, 'state) state -> ('b, 'state) state

(** Map through the elements of a list, threading state from left to right. *)
val map_list : f:('a -> ('b, 'state) state) -> 'a list -> ('b list, 'state) state

(** A State-aware wrapper around Debug. *)
module Debug : sig
  val span : (('a * 'state) Debug.presult -> unit) -> (unit -> ('a, 'state) state) -> ('a, 'state) state

  val presult_value : ('a * 'state) Debug.presult -> 'a Debug.presult
  val presult_state : ('a * 'state) Debug.presult -> 'state Debug.presult

  val (let@) : ('a -> 'b) -> 'a -> 'b
end

