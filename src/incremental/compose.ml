
let compose f g x 
(*@
  ex r_g; g(x, r_g);
  ex r_f; f(r_g, r_f);
  Norm (emp, r_f)
@*)
= f (g x)

(*
let f x 
(*@ ex z;
    req x -> z;
    ens Norm(x->z+1 /\ ret = z +1, ret) @*)
= x := !x + 1; x

let g x 
(*@ ex z;
    req x -> z;
    ens Norm(x->z*2 /\ ret = z*2, ret) @*)
= x:= !x * 2; x 

let caller2 ()
(*@
ex x;
ens Norm(x->4, 4) @*)
= let x = ref 1 in 
  compose g f x 

let caller1 () 
(*@
ex x;
ens Norm(x->3, 3) @*)
= let x = ref 1 in
  compose f g x
*)