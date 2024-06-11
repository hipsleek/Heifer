
let undelimited () =
  1 + shift k 1

let hello ()
(*@ ens res=1 @*)
= reset (1 + shift k 1)

let hello1 ()
(*@ ens res=2 @*)
= reset (1 + shift k (k 1))

let hello3 ()
(*@ ens res=3 @*)
= let f x = x + x in
  reset (1 + shift k (k (f 1)))

let hello4 ()
(*@ ens res=4 @*)
= let f x = x + x in
  (reset (shift k (fun x -> k (f x)))) 2

(* let get_int () =
  shift k (fun x -> k x)

let main () =
  (reset (get_int () ^ get_int ())) "a" "b" *)

(* let hello_lambda ()
(*@ ens res=4 @*)
= let f x = x + x in
  (fun x -> x) 2 *)
