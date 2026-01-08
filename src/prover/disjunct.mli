(** Tactics to handle disjunctions on the lhs and on the rhs of an entailment.

    Disjunction plays a dual role. On the left, we need to [destruct] it and
    attempt a case analysis. On the right, we need to pick one of the branches,
    either [left] branch or [right] branch.

    In a nutshell, the way we handle disjunction is similar to how we deal with
    it in proof assistant like Rocq: if the disjunction is in the hypothesis,
    we [destruct] it and then handle two new generated subcases. if the
    disjunction is in the goal, we prove either [left] or [right] branch. *)

open Core.Syntax

exception Destruct_failure
exception Left_failure
exception Right_failure

(** Destruct a disjunction on the lhs, generates two new subgoals.

    Raise [Destruct_failure] if this is not applied on a disjunction. *)
val disjunct_destruct : staged_spec -> staged_spec * staged_spec

(** Pick the left branch of a disjunction on the rhs.

    Raise [Left_failure] if this is not applied on a disjunction. *)
val disjunct_left : staged_spec -> staged_spec

(** Pick the right branch of a disjunction on the rhs.

    Raise [Right_failure] if this is not applied on a disjunction. *)
val disjunct_right : staged_spec -> staged_spec
