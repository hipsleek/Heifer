
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let[@pure] rec at (xs: int list) (i: int): int
= match xs with
  | [] -> 0
  | x :: xs' -> if i = 0 then x else at xs' (i - 1)

(* Example 6.5 *)
let[@pure] rec find (xs: int list) (y: int): int
= match xs with
| [] -> 0
| x :: xs' -> if x = y then 0 else 1 + find xs' y

let test_find_index xs y
(*@ req length(xs)>=0; ens res>=0/\res<=length(xs) @*)
= find xs y

let test_at_find xs y (* FIXME *)
(*@
  ex r; ens r=length(xs)/\res=r
  \/ ex r; ens at(xs,r)=y/\res=r
@*)
= find xs y
