
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

(* Example 6.4 *)
let[@pure] rec at (xs: int list) (i: int): int
(*@ req i>=0/\i<length(xs) @*)
= match xs with
  | [] -> 0
  | x :: xs' -> if i = 0 then x else at xs' (i - 1)
