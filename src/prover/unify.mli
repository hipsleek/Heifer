open Core.Syntax

exception Unification_failure

(** The main entry point of the unification algorithm. [unify lhs target uvars]
    tries to unify [lhs] with [target], with unification variables [uvars].

    Raise [Unification_failure] if fail. *)
val unify : term -> term -> TVSet.t -> term TVMap.t * (term -> term) option
