open Types

(* we need this module because https://dune.readthedocs.io/en/stable/variants.html#:~:text=It%E2%80%99s%20not%20possible%20for%20implementations%20to%20introduce%20new%20public%20modules *)

let entailConstrains pi1 pi2 =
  let sat = not (Provers.askZ3 (Not (Or (Not pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat
