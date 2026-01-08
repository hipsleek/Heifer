open Bindlib
open Core.Syntax

type induction_hypothesis = (term, prop) mbinder

(** Generates an induction hypothesis (disregarding termination measure at the
    moment), just like the [fix] tactic in Rocq.

    This method takes a list of pure assumptions (the current context), the
    lhs, the rhs, and a list of variables to generalize over.

    TODO: prove a measure for well-foundness, which should be encoded as
    another implication. If we decide to encode a list of heap assumptions like
    Iris, we will also need to generalize over these variables; and we will
    need the magic wand. *)
val induction : prop list -> term mvar -> staged_spec -> staged_spec -> induction_hypothesis
