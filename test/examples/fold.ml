(* let rec length li =
  match li with
  | [] -> 0
  | x :: xs -> 1 + length xs
*)

let [@pure] hello (x:int) : int = x + 1

let pure_hello ()
(*@ ens res=hello(2) @*)
= 3

let [@pure] rec sum (li: int list) : int =
  match li with
  | [] -> 0
  | x :: xs -> x + sum xs

(*
let rec foldl f li acc =
  match li with
  | [] -> acc
  | x :: xs ->
    let acc' = f x acc in
    foldl f xs acc'

let foldl_sum xs k
(*@ ex r. sum(xs, r); ens res=r+k @*)
= let g c t = c + t in
  foldl g xs k

let foldl_length xs init
(*@ ex r. length(xs, r); ens res=r+init @*)
= let g c t = 1 + t in
  foldl g xs init *)

let rec foldr f li acc =
  match li with
  | [] -> acc
  | x :: xs ->
    f x (foldr f xs acc)

let foldr_sum xs k
(*@ ens res=sum(xs)+k @*)
= let g c t = c + t in
  foldr g xs k

(* let foldr_length xs init
(*@ ex r. length(xs, r); ens res=r+init @*)
= let g c t = 1 + t in
  foldr g xs init *)
