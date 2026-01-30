open Core.Syntax

exception Rewrite_failure of string

type rewrite_direction =
  | Direction_ltr
  | Direction_rtl

type rewrite_relation =
  | Relation_eq
  | Relation_subsumes

module Direction : sig
  val ltr : rewrite_direction
  val rtl : rewrite_direction
end

(** A rewriting rule is of the form:
    {[
      forall x. cond x => forall y. cond x y => ... => lhs x y "rel" rhs x y
    ]}
    - [x] and [y] are universally quantified variables, which will be instantiated by unification.
      Therefore, they are also called `unification` variables.
    - [cond x] and [cond x y] are rewriting conditions, to be proven before the rewriting is done.
    - [rel] is a relation, either subsumption [<:] or equality [=]. *)
type rewrite_rule

(** Turn a term into a [rule], or raise [Invalid_argument]. *)
val make_rule : ?direction:rewrite_direction -> term -> rewrite_rule

val get_rule_relation : rewrite_rule -> rewrite_relation

val get_rule_conditions : rewrite_rule -> term list

val get_rule_lhs : rewrite_rule -> term

val get_rule_rhs : rewrite_rule -> term

type rewrite_state

module Monad : sig
  type 'a t
  val run : 'a t -> rewrite_state -> 'a * rewrite_state
  val pure : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapl : 'b -> 'a t -> 'b t
  val lift2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t
  val ( <$ ) : 'b -> 'a t -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val get : rewrite_state t
  val put : rewrite_state -> unit t
  val modify : (rewrite_state -> rewrite_state) -> unit t
end

(** Traverse the target and rewrite using the given rule everywhere in it.
    Produces subgoals if the rule is conditional.

    Raise [Rewrite_failure] if no change was made. *)
val rewrite : rewrite_rule -> term -> term * term list
