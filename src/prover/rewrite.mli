open Bindlib
open Core.Syntax

exception Rewrite_failure

(** A rewriting rule is of the form:
    {[forall x y z, lhs x y z => rhs x y z]}
    where arrow can be replaced by some other relation, like equality or
    entailment.

    At the moment, we enforce that the rewriting rule is closed.

    TODO: should relax rewriting rule to include free variables (which may
    come from the proof context, for example). Also, we may want "conditional
    rewriting" of the form:
    {[forall x y z, cond x y z -> lhs x y z => rhs x y z]}
    *)
type rule = (term, staged_spec * staged_spec) mbinder

(** Rewrite a [staged_spec] according to a [rule]. The lhs of the [rule] must
    match exactly the [staged_spec] to be written.

    Raise [Rewrite_failure] if rewriting cannot be done *)
val rewrite_exact : rule -> staged_spec -> staged_spec

val rewrite : rule -> staged_spec -> staged_spec
