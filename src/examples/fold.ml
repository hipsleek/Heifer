let rec length li =
  match li with
  | [] -> 0
  | x :: xs -> 1 + length xs

let rec sum li =
  match li with
  | [] -> 0
  | x :: xs -> x + sum xs

let rec foldl f li acc =
  match li with
  | [] -> acc
  | x :: xs ->
    let acc' = f x acc in
    foldl f xs acc'

let foldl_sum xs k
(*@ ex r; sum(xs, r); ens res=r+k @*)
= let g c t = c + t in
  foldl g xs k

let foldl_length xs init
(*@ ex r; length(xs, r); ens res=r+init @*)
= let g c t = 1 + t in
  foldl g xs init

let foldl_length_state x xs init
(*@ ex i; req x->i; ex r; length(xs, r); ens x->i+r/\res=r+init @*)
= let g c t = x := !x + 1; 1 + t in
  foldl g xs init

let foldl_sum_state x xs init
(*@ ex i; req x->i; ex r; sum(xs, r); ens x->i+r/\res=r+init @*)
= let g c t = x := !x + c; c + t in
  foldl g xs init

let rec foldr f li acc =
  match li with
  | [] -> acc
  | x :: xs ->
    f x (foldr f xs acc)

let foldr_sum xs k
(*@ ex r; sum(xs, r); ens res=r+k @*)
= let g c t = c + t in
  foldr g xs k

let foldr_length xs init
(*@ ex r; length(xs, r); ens res=r+init @*)
= let g c t = 1 + t in
  foldr g xs init

let foldr_length_state x xs init
(*@ ex i; req x->i; ex r; length(xs, r); ens x->i+r/\res=r+init @*)
= let g c t = x := !x + 1; 1 + t in
  foldr g xs init

let foldr_sum_state x xs init
(*@ ex i; req x->i; ex r; sum(xs, r); ens x->i+r/\res=r+init @*)
= let g c t = x := !x + c; c + t in
  foldr g xs init
