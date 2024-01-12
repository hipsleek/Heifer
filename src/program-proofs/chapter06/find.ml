
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

(* let[@pure] rec at (xs: int list) (i: int): int
(*@ req i>=0/\i<length(xs) @*)
= match xs with
  | [] -> 0
  | x :: xs' -> if i = 0 then x else at xs' (i - 1) *)

(* Example 6.5 *)
let[@pure] rec find (xs: int list) (y: int): int
(*@ ex r; ens r>=0/\r<=length(xs)/\res=r @*)
= match xs with
| [] -> 0
| x :: xs' -> if x = y then 0 else 1 + find xs' y

(* let[@pure] at_find (xs: int list) (y: int): int
(*@
  ex r; ens r=length(xs)/\res=r
  \/ ex r; ens at(xs, r)=y/\res=r
@*)
= find xs y *)
