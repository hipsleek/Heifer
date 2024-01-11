
(* Example 6.1 *)
let[@pure] rec length (xs: int list): int
(*@ ens res>=0 @*)
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let[@pure] rec snoc (lst: int list) (x: int): int list =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

let[@pure] length_snoc (xs: int list) (x: int): int
(*@ ens res=length(xs)+1 @*)
= length (snoc xs x)

(* Example 6.2 *)

let[@pure] rec append (xs: int list) (ys: int list): int list =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys
  
let[@pure] length_append (xs: int list) (ys: int list): int
(*@ ens res=length(xs)+length(ys) @*)
= length (append xs ys)

let[@pure] append_nil (xs: int list): int list
(*@ ens res=xs @*)
= append xs []    

(* TODO: Associativity of append *)

(* Example 6.3 *)
let[@pure] rec take (xs: int list) (n: int): int list
(*@ req n>=0/\n<=length(xs) @*)
= if n = 0 then [] else match xs with
| [] -> []
| x :: xs' -> x :: take xs' (n - 1)

let[@pure] rec drop (xs: int list) (n: int): int list
(*@ req n>=0/\n<=length(xs) @*)
= if n = 0 then xs else match xs with
| [] -> []
| x :: xs' -> drop xs' (n - 1)

let[@pure] append_take_drop (xs: int list) (n: int): int list
(*@ req n>=0/\n<=length(xs); ens res=xs @*)
= append (take xs n) (drop xs n)

let[@pure] take_drop_append1 (xs: int list) (ys: int list)
(*@ ens res=xs @*)
= take (append xs ys) (length xs)

let[@pure] take_drop_append2 (xs: int list) (ys: int list)
(*@ ens res=ys @*)
= drop (append xs ys) (length xs)
