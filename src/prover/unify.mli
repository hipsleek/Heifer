open Core.Syntax

exception Unification_failure of string

val unify_in : term -> term -> TVSet.t -> term TVMap.t -> term TVMap.t
val unify_assoc_in : term -> term -> TVSet.t -> term TVMap.t -> term TVMap.t * (term -> term) option

(** The main entry point of the unification algorithm. [unify lhs target uvars] tries to unify [lhs]
    with [target], using unification variables [uvars].

    Raise [Unification_failure] if fail. *)
val unify : term -> term -> TVSet.t -> term TVMap.t

(** [unify_assoc lhs target uvars] tries to unify [lhs] with [target] modulo associativity of
    [Sequence] and [Bind], using unification variables [uvars]. This function additionally returns a
    frame of type [(term -> term) option], which can be used to construct a modified version of
    [target] where the unmatched subterms are preserved.

    Raise [Unification_failure] if fail. *)
val unify_assoc : term -> term -> TVSet.t -> term TVMap.t * (term -> term) option
