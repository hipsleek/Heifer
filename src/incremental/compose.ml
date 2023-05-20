
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
    Norm(x->z+1, x) @*)
= x := !x + 1; x

let g x 
(*@ ex u;
    req x->u;
    ex ret;
    Norm(ret=u+u/\x->u+u, x) @*)
= x := !x + !x; x

let caller1 () 
(*@ ex w; Norm(w->4, 4) @*)
= let x = ref 1 in
  let y1 = compose f g x in
  !y1

let caller2 ()
(*@ ex w; Norm(w->3, 3) @*)
= let y = ref 1 in 
  let y1 = compose g f y in
  !y1
