open Core.Syntax

exception Unification_failure

(** The main entry point of the unification algorithm. [unify lhs target uvars]
    tries to unify [lhs] with [target], with unification variables [uvars]. At
    the moment, we only allow unification variables to unify with [term].

    Raise [Unification_failure] if fail. *)
val unify : staged_spec -> staged_spec -> TVSet.t -> term TVMap.t
