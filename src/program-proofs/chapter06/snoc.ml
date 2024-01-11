
let[@pure] rec length (xs: int list): int
(*@ ens res>=0 @*)
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let[@pure] rec snoc (lst: int list) (x: int): int list =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

let[@pure] length_snoc (xs: int list) (x: int): int
(*@ ens res=length(xs)+1 @*)
= length (snoc xs x)
