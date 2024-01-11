
(* https://github.com/FabianWolff/closure-examples/blob/master/repeat_with_n.rs *)
let rec repeat_with_n f n =
  if n = 0 then []
  else f () :: repeat_with_n f (n - 1)

let rec integers n =
  if n <= 0 then []
  else n :: integers (n - 1)

let test1 n (* FIXME *)
(*@ ex r; integers(n, r); ens res=r @*)
= let c = ref 0 in
  let cl () = c := !c + 1; !c in
  repeat_with_n cl n
