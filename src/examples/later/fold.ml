
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

(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/fold.rs*)
let rec all xs pred =
  match xs with
  | [] -> true
  | x :: xs' -> pred x && all xs' pred

let foldr_all xs pred (* FIXME *)
(*@ ex r; all(xs, pred, r); ens res=r @*)
= let f a c = pred a && c in
  foldr f xs true

(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/fold.rs*)
let rec any xs pred =
  match xs with
  | [] -> false
  | x :: xs' -> pred x || any xs' pred

let foldr_any xs pred (* FIXME *)
(*@ ex r; any(xs, pred, r); ens res=r @*)
= let f a c = pred a || c in
  foldr f xs true
