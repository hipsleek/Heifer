
let[@pure] rec length (li:int list) : int = 
  match li with 
  | [] -> 0
  | x :: xs -> 1 + length xs

(*@
  lemma length_length xs res =
    length(xs, res) ==> ens res=length(xs)
@*)

let length_length xs
(*@ ens res=length(xs) @*)
= length xs

let rec foldr f li acc =
  match li with 
  | [] -> acc 
  | x :: xs -> 
    let acc' = f x acc in 
    foldr f xs acc'

let foldr_length xs init
(*@ ex r; ens res=length(xs)+init @*)
= let g c t = 1 + t in
  foldr g xs init

let rec append (xs: int list) (ys: int list): int list =
match xs with
| [] -> ys
| x :: xs' -> x :: append xs' ys

let append_length (xs: int list) (ys: int list): int
(*@ ens res=length(xs)+length(ys) @*)
= length (append xs ys)

let rec snoc (lst: int list) (x: int): int list =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

let snoc_length (xs: int list) (x: int): int
(*@ ens res=length(xs)+1 @*)
= length (snoc xs x)
