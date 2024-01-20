
let rec length xs =
  match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

(*@
  lemma length_positive_l xs res =
    length(xs, res) ==> ens res>=0
@*)

(*@
  lemma length_empty res =
    length([], res) ==> ens res=0
@*)

let length_positive xs
(*@ ens res>=0 @*)
= length xs
