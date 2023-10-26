open Printf

effect Exchange : int -> int
let l = ref 5

let exchange (m:int)
= perform (Exchange m)

let exc_handler (l:int ref) (new_v:int)
=  match exchange new_v with
  | x -> x
  | exception e -> raise e
  | effect (Exchange n) k ->
     let old_v = !l in
     l := n;
     continue k old_v

let _ =
  let i = exc_handler l 10 in
  printf "%d\n" i ;
  let i = exc_handler l 10 in
  printf "%d\n" i
