let rec length xs =
  match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let length_positive xs
(*@ ex r; ens r>=0; Norm(emp, r) @*)
= length xs