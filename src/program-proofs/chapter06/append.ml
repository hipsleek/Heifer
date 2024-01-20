
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

let length_append xs ys (* FIXME *)
(*@ ens res=length(xs)+length(ys) @*)
= length (append xs ys)
