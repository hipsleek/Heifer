open Core.Syntax

exception Unification_failure of string

(** The main entry point of the unification algorithm. [unify lhs rhs uvars] tries to unify [lhs]
    with [rhs], using unification variables [uvars].

    Raise [Unification_failure] if fail. *)
val unify : term -> term -> TVSet.t -> term TVMap.t

(** [unify_assoc lhs rhs uvars] tries to unify [lhs] with [rhs] modulo associativity of [Sequence]
    and [Bind], using unification variables [uvars]. This function additionally returns a frame of
    type [(term -> term) option], which can be used to construct a modified version of [rhs] where
    the unmatched subterms are preserved.

    Raise [Unification_failure] if fail. *)
val unify_assoc : term -> term -> TVSet.t -> term TVMap.t * (term -> term) option

(** [unify_in lhs rhs uvars sigma] tries to unify [lhs] with [rhs], using unification variables
    [uvars] and partial substitution [sigma]. This function may be used when the values of some
    unification variables are known in advance - these values will be verified against [rhs].

    Raise [Unification_failure] if fail. *)
val unify_in : term -> term -> TVSet.t -> term TVMap.t -> term TVMap.t

(** See [unify_assoc] and [unify_in].

    Raise [Unification_failure] if fail. *)
val unify_assoc_in : term -> term -> TVSet.t -> term TVMap.t -> term TVMap.t * (term -> term) option
