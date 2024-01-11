
let[@pure] rec length (xs: int list): int
(*@ ens res>=0 @*)
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

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
