open Bindlib
open Core.Syntax

type induction_hypothesis = (term, prop) mbinder

(** Generates an induction hypothesis, given a list of pure assumptions (the
    current context), the lhs, the rhs, and a list of variables to generalize
    over. *)
val induction :
  [ `List | `Int of int ] ->
  term var ->
  term mvar ->
  prop list ->
  staged_spec ->
  staged_spec ->
  induction_hypothesis
