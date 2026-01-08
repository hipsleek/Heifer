open Bindlib
open Core.Syntax
open Core.Syntax_util

type induction_hypothesis = (term, prop) mbinder

(** Generates an induction hypothesis (disregarding termination measure) at the
    moment, just like the [fix] tactic in Rocq.

    This method takes a list of pure assumptions (the current context), the lhs,
    the rhs, and a list of variables to generalize over.

    TODO: prove a measure for well-foundness, which should be encoded as another
    implication. *)
let induction (assumptions : prop list) (uvars : term mvar) lhs rhs : induction_hypothesis =
  let uvars_set = TVSet.of_seq (Array.to_seq uvars) in
  let generalized_assumptions = List.filter (prop_has_vars uvars_set) assumptions in
  (* Technically, `subsume` should live at meta-logic and not inside the logic system itself *)
  let ih = List.fold_right (fun h g -> PImplies (h, g)) generalized_assumptions (PSubsumes (lhs, rhs)) in
  (* Now generalize ih *)
  unbox (bind_mvar uvars (box_prop ih))
