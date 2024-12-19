
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

(* Example 6.2 *)

let rec append xs ys =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

let append_nil xs
(*@ ens res=xs @*)
= append xs []    

external length_append : int list -> int list -> int list -> bool = "append.Extras.length_append"

let test_length_append xs ys
(*@ ens length_append(xs,ys,res)=true @*)
= append xs ys
