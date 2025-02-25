let either a b =
  shift k (k a; k b)

let main ()
(*@ ens res = 10 @*)
= let r = ref 0 in
  (reset (let x = either 1 2 in r := !r + x));
  (reset (let x = either 3 4 in r := !r + x));
  !r
