
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let rec snoc lst x =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

(* Example 6.6 *)
let rec reverse xs =
  match xs with
  | [] -> []
  | x :: xs' -> snoc (reverse xs') x 

let length_reverse xs (* FIXME *)
(*@ ens res=length(xs) @*)
= length (reverse xs)
