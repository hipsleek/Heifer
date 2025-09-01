type meta_assumption =
  | ShiftFree of string (* name of the function that is shift-free *)

(* we need a function that checks for shift-freedom *)
(* lemma : cond -> rule *)
(* we need a function that, when trying to fire the lemma, check the condition before doing such a thing *)
(* is this similar to trigger? *)
