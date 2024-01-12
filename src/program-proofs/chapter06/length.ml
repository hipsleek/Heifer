
(* Example 6.1 *)
let rec length xs
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let length_positive xs
(*@ ens res>=0 @*)
= length xs
