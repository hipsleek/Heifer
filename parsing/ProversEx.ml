open Types

let entailConstrains pi1 pi2 =
  let sat = not (Provers.askZ3 (Not (Or (Not pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat
