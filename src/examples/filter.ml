
(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/filter.rs *)
let rec filter xs pred =
  match xs with
  | [] -> []
  | y :: ys -> if pred y then y :: filter ys pred else filter ys pred

let is_even x = x mod 2 = 0

let evens () (* FIXME *)
(*@ ex i; Norm(i->[0;1;2;3], [0;2]) @*)
= let lst = ref [0; 1; 2; 3] in
  filter !lst is_even
