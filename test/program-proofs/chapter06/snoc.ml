
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let rec snoc lst x =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

external length_snoc : int list -> int -> int list -> bool = "snoc.Extras.length_snoc"

let length_snoc xs x
(*@ ens length_snoc(xs, x, res)=true @*)
= snoc xs x
