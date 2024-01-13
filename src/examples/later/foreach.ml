
(* https://github.com/FabianWolff/closure-examples/blob/master/for_each.rs *)
let rec foreach xs f =
  match xs with
  | [] -> ()
  | y :: ys -> f y; foreach ys f

let incr v = v := !v + 1

let do_nothing v = ()

let foreach_example x
(*@ ex v1; req x->v1; ens x->v1 @*)
(*
  Can be temporarily fixed by increasing the unfolding bound for do_nothing.
  This workaround does not work for incr.
*)
= foreach [x] do_nothing;
