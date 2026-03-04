  
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


(* OCaml List Module: https://v2.ocaml.org/api/List.html *)

(* https://v2.ocaml.org/api/List.html#VALfind_index *)
let rec find_index lst y =
  match lst with
  | [] -> 0
  | x :: xs -> if x = y then 0 else 1 + (find_index xs y)

(* https://v2.ocaml.org/api/List.html#VALexists *)
let rec exists lst f =
  match lst with
  | [] -> false
  | x :: xs -> f x || exists xs f

(* https://v2.ocaml.org/api/List.html#VALint *)
let init len f =
  if len < 0 then perform Invalid_argument;
  let rec aux idx
  = if idx = len then []
    else let k = f idx in k :: aux (idx + 1)
  in
  aux 0

(* https://v2.ocaml.org/api/List.html#VALequal *)
let rec equal xs ys =
  match xs with
  | [] -> (
    match ys with
    | [] -> true
    | y :: ys' -> false
  )
  | x :: xs' -> (
    match ys with
    | [] -> false
    | y :: ys' -> x = y && equal xs' ys'
  )
