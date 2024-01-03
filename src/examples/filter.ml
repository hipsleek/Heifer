
(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/filter.rs *)
let rec filter xs pred =
  match xs with
  | [] -> []
  | y :: ys -> if pred y then y :: filter ys pred else filter ys pred

let is_positive x = x > 0

let positives () (* FIXME *)
(*@ ens res=[1; 2] @*)
(* Can be temporarily fixed by increasing the unfolding bound for do_nothing *)
= filter [0; 1; 2; (-1)] is_positive
