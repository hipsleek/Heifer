type tactic =
  | Unfold_right
  | Unfold_left
  | Apply of string
  | Case of int * tactic

