
let[@pure] rec length (li:int list) : int = 
  match li with 
  | [] -> 0
  | x :: xs -> 1 + length xs

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
