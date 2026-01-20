open Core.Syntax

(** A rewriting rule is of the form:
    {[
      forall x y z, cond x y z => ... => lhs x y z <: rhs x y z
    ]}
    where [<:] can be replaced by some other relation, like equality.

    At the moment, we enforce that the rewriting rules are closed.

    TODO: should relax rewriting rule to include free variables (which may come
    from the proof context, for example). *)
type rule

(** Turn a prop into a [rule], or raise [Invalid_argument]. *)
val prop_to_rule : prop -> rule

(** Traverse the target and rewrite using the given rule everywhere in it.
    Produces subgoals if the rule is conditional. *)
val rewrite : rule -> staged_spec -> (staged_spec * prop list) option
