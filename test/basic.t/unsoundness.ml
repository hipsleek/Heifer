

let rec f1 ()
= f1 ()

(* this is currently okay because unfolding (using rewriting) makes no progress, and so stops *)
let f1_false ()
(*@ ens false @*)
= f1 ()

let rec f2 n
= f2 (n-1)

let f2_false n
(*@ ens false @*)
= f2 n
