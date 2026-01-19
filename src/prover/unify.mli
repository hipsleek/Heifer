open Core.Syntax

exception Unification_failure
exception Unification_frame of term TVMap.t * (term -> term)

(** The main entry point of the unification algorithm. [unify lhs target uvars]
    tries to unify [lhs] with [target], with unification variables [uvars].

    Raise [Unification_failure] if fail. *)
val unify : staged_spec -> staged_spec -> TVSet.t -> term TVMap.t
