open Hipcore
open Hiptypes

(** [solve vars h1 h2] solves the biabduction problem {m A * H_1 \vdash H_2 * F}.
  [vars] is a list of existentially quantified variables.
  Returns {m A}, {m F}, and extra conditions for {m F}.
  Throws [Norm_failure] if there is no solution.
*)
(* val solve : string list -> state -> state -> pi * kappa * pi * kappa * pi *)
