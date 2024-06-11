
let hello_lambda ()
(*@ ens res=2 @*)
= (fun x -> x) 2

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

let hello41 ()
(*@ ens res=4 @*)
= let f x = x + x in
  (reset (shift k (fun x -> k (f x)))) 2

let hello4 ()
(*@ ens res=4 @*)
= (reset (shift k (fun x -> k x))) 4

let hello5 ()
(*@ ens res=5 @*)
= (reset (shift k (fun x -> k x) + 2)) 3

let hello6 ()
(*@ ens res=6 @*)
= ((reset (shift k (fun x -> k x) + shift k (fun x -> k x))) 2) 4

let hello7 ()
(*@ ens res=7 @*)
= ((reset (shift k (fun x -> k x) + shift k (fun x -> k x))) 6) 1

let hello_eta ()
(*@ ens res=2 @*)
= (reset (shift k k)) 2

let hello8 ()
(*@ ens res=8 @*)
= ((reset (shift k k + shift k k)) 3) 5

let hello_string ()
(*@ ens res="a" @*)
= "a"

let hello_string_conc ()
(*@ ens res="a" ++ "b" @*)
= "a" ^ "b"

(* let main1 ()
(*@ ens res=3 @*)
= let get_int () = shift k (fun x -> k x) in
  ((reset (get_int () + 1)) 2) *)

  (* ((reset (get_int () + get_int ())) 1) 2 *)

(* ((reset (get_int () ^ get_int ())) "a") "b" *)

(* shift k k *)

(* let get_int () = shift k (fun x -> k x)

let main1 ()
(*@ ens res=3 @*)
= ((reset (get_int () + 1)) 2) *)
