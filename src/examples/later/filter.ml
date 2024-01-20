
(* https://github.com/FabianWolff/closure-examples/blob/master/filter.rs *)
let rec filter xs pred =
  match xs with
  | [] -> []
  | y :: ys -> if pred y then y :: filter ys pred else filter ys pred

let rec all_positive xs =
  match xs with
  | [] -> true
  | x :: xs' -> x > 0 && all_positive xs'

let positives xs
(*@ ex ys r; all_positive(ys, r); ens r=true/\res=ys @*)
= let is_positive x = x > 0 in
  filter xs is_positive
