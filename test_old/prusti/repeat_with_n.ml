
(* https://github.com/FabianWolff/closure-examples/blob/master/repeat_with_n.rs *)

let rec repeat_with_n f n =
  if n = 0 then []
  else let k = f () in k :: repeat_with_n f (n - 1)

let rec repeat x n =
  if n = 0 then []
  else x :: repeat x (n - 1)

let rec range l r =
  if l = r then [l]
  else if l > r then []
  else l :: range (l + 1) r

let test1 n c
(*@ ex r i; req c->i; repeat(1, n, r); ens c->i+n/\res=r @*)
= let cl () = c := !c + 1; 1 in
  repeat_with_n cl n

let test2 n c
(*@ ex r i; req c->i/\n>=1; range(i+1, i+n, r); ens c->i+n/\res=r @*)
= let cl () = c := !c + 1; !c in
  repeat_with_n cl n
