let either a b =
  shift k (k a; k b)

let main ()
(*@ ens res = 3 @*)
= let r = ref 0 in
  (reset (let x = either 1 2 in r := !r + x));
  (* (reset (let x = either 3 4 in r := !r + x)); *)
  (* if we add the line above, heifer will throw an error in verification time *)
  !r
