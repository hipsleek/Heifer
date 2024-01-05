
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

let rec exists xs f =
  match xs with
  | [] -> false
  | x :: xs' -> f x || exists xs' f

let foldr_exists xs pred (* FIXME *)
(*@ ex r; exists(xs, pred, r); ens res=r @*)
= let f x acc = pred x || acc in
  foldr f xs false

let foldr_length xs init
(*@ ex r; length(xs, r); Norm(emp, r+init) @*)
= let g c t = 1 + t in
  foldr g xs init

let foldr_length_state x xs init
(*@ ex i; req x->i; ex r; length(xs, r); Norm(x->i+r, r+init) @*)
= let g c t = x := !x + 1; 1 + t in
  foldr g xs init

let rec sum li = 
  match li with 
  | [] -> 0
  | x :: xs -> x + sum xs

let foldr_sum xs init
(*@ ex r; sum(xs, r); Norm(emp, r+init) @*)
= let g c t = c + t in
  foldr g xs init

let foldr_sum_state x xs init
(*@ ex i; req x->i; ex r; sum(xs, r); Norm(x->i+r, r+init) @*)
= let g c t = x := !x + c; c + t in
  foldr g xs init

(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/fold.rs*)
let foldr_all () (* FIXME *)
(*@ ens res=false @*)
= let xs = [1; 0; 1] in
  let f a c = a == 1 && c in
  foldr f xs true

(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/fold.rs*)
let foldr_any () (* FIXME *)
(*@ ens res=false @*)
= let xs = [1; 0; 1] in
  let f a c = a == 1 || c in
  foldr f xs false
