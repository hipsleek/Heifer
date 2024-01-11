  
let rec subsequence sub lst =
  match sub with
  | [] -> true
  | y :: ys -> match lst with
    | [] -> false
    | x :: xs -> (x = y && subsequence ys xs) || subsequence sub xs

let rec replace lst x y =
  match lst with
  | [] -> []
  | h :: tail -> if h = x then y :: replace tail x y else h :: replace tail x y

let rec interleave xs ys =
  match xs with
  | [] -> ys
  | x :: xs' -> match ys with
  | [] -> xs
  | y :: ys' -> x :: (y :: interleave xs' ys')


(* List scanning/searching: https://v2.ocaml.org/api/List.html *)

(* Returns the index of y in lst if it exists, or the length of lst *)
let rec find_index lst y =
  match lst with
  | [] -> 0
  | x :: xs -> if x = y then 0 else 1 + (find_index xs y)

let rec exists lst f =
  match lst with
  | [] -> false
  | x :: xs -> f x || exists xs f
