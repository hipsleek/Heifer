
let compose f g x 
(*@
  ex r_g; g(x, r_g);
  ex r_f; f(r_g, r_f);
  Norm (emp, r_f)
@*)
= f (g x)

let f x 
(*@ ex z;
    req x->z;
    ex ret;
    Norm(ret=z+1/\x->ret, ret) @*)
= x := !x + 1; !x

let g x 
(*@ ex z;
    req x->z;
    ex ret;
    Norm(ret=z+z/\x->z+z, ret) @*)
= x:= !x + !x; !x

(*

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