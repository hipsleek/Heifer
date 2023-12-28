
(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/for_each.rs *)

let rec foreach xs f =
  match xs with
  | [] -> ()
  | y :: ys -> f y; foreach ys f

let foreach_example () (* FIXME *)
(*@ ex x; ex y; ex z; Norm(x->1*y->2*z->3) @*)
= let x = ref 0 in
  let y = ref 1 in
  let z = ref 2 in
  let incr v = v := !v + 1 in
  foreach [x; y; z] incr;
