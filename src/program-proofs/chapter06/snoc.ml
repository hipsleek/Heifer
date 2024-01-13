
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let rec snoc lst x =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

let length_snoc xs x (* FIXME *)
(*@ ens res=length(xs)+1 @*)
= length (snoc xs x)
