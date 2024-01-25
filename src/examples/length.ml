
let[@pure] rec length (xs:int list): int =
  match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

(*@
  lemma length_positive_l xs res =
    length(xs, res) ==> ens res>=0
@*)

(*@
  lemma length_empty res =
    length([], res) ==> ens res=0
@*)

let length_positive xs
(*@ ens res>=0 @*)
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