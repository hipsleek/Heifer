
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

(* let main1 () =
  1 + shift k (fun x -> k (i2s x)) *)