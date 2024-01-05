
(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/repeat_with_n.rs *)
let rec repeat_with_n f n =
  if n = 0 then []
  (* Currently, this is a cons instead of a snoc *)
  else f () :: repeat_with_n f (n - 1)

let test1 () (* FIXME *)
(*@ ens res=[18;16;14;12] @*)
= let c = ref 5 in
  let cl () = c := !c + 1; !c + !c in
  repeat_with_n cl 4
