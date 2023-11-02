
effect Exchange : int -> int

let exchange (m:int)
(*@ ex r; Exchange(emp, m, r); Norm(res=r) @*)
= perform (Exchange m)

let exc_handler (l:int ref) (new_v:int)
(*@ ex z; req l->z; Norm(l->new_v, z) @*)
=  match exchange new_v with
  | x -> x
  | exception e -> raise e
  | effect (Exchange n) k ->
     let old_v = !l in
     l := n;
     continue k old_v

let test () 
(*@ ex l;  Norm(l->10, 5) @*)
= let l = ref 5 in
  let i = exc_handler l 10 in
  i
