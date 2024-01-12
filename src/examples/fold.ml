
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
(*@ ex r; length(xs, r); ens res=r+init @*)
= let g c t = 1 + t in
  foldr g xs init

let foldr_length_state x xs init
(*@ ex i; req x->i; ex r; length(xs, r); ens x->i+r/\res=r+init @*)
= let g c t = x := !x + 1; 1 + t in
  foldr g xs init

let rec sum li = 
  match li with 
  | [] -> 0
  | x :: xs -> x + sum xs

let foldr_sum xs init
(*@ ex r; sum(xs, r); ens res=r+init @*)
= let g c t = c + t in
  foldr g xs init

let foldr_sum_state x xs init
(*@ ex i; req x->i; ex r; sum(xs, r); ens x->i+r/\res=r+init @*)
= let g c t = x := !x + c; c + t in
  foldr g xs init
