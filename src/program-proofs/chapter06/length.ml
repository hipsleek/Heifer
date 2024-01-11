
(* Example 6.1 *)
let[@pure] rec length (xs: int list): int
(*@ ens res>=0 @*)
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1
