open Core.Syntax

exception Destruct_failure
exception Left_failure
exception Right_failure

(** Destruct a disjunction on the left branch, generates two new subgoals.
    Raise [Destruct_failure] if this is not applied on a disjunction. *)
let disjunct_destruct target =
  match target with
  | Disjunct (s1, s2) -> s1, s2
  | _ -> raise Destruct_failure

let disjunct_left target =
  match target with
  | Disjunct (s, _) -> s
  | _ -> raise Left_failure

let disjunct_right target =
  match target with
  | Disjunct (_, s) -> s
  | _ -> raise Right_failure
