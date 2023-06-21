
let rec length li = 
  match li with 
  | [] -> 0
  | x :: xs -> 1 + length xs

let rec foldr f li acc =
  match li with 
  | [] -> acc 
  | x :: xs -> 
    let acc' = f x acc in 
    foldr f xs acc'

let foldr_length xs init
(*@ ex r; length(xs, r); Norm(emp, r+init) @*)
=
  let g c t = 1 + t in
  foldr g xs init

let rec sum li = 
  match li with 
  | [] -> 0
  | x :: xs -> x + sum xs

let foldr_sum xs init
(*@ ex r; sum(xs, r); Norm(emp, r+init) @*)
=
  let g c t = c + t in
  foldr g xs init