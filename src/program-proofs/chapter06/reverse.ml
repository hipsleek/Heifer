

let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let[@pure] rec snoc (lst: int list) (x: int): int list =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

(* Example 6.6 *)
let[@pure] rec reverse (xs: int list): int list =
  match xs with
  | [] -> []
  | x :: xs' -> snoc (reverse xs') x 

let[@pure] length_reverse (xs: int list): int
(*@ ens res=length(xs) @*)
= length (reverse xs)