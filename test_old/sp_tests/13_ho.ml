
(* f (g x) *) 
let compose f g x 
(*@ ex rf rg;
   G(emp, ret_g);
   F(ret_g, ret_f);
   Norm(emp, ret_f)
@*)
= let ret = g x in 
  f ret 
  

let f x 
(*@
  ex z;
  req x-> z; 
  Norm(x->z+1, x)
@*)
= x := !x + 1; x


let g x 
(*@  
  ex z;
  req x -> z; 
  Norm(x->z * 2, x)
@*)
= x:= !x * 2; x

let main = 
  let x = ref 1 in 
  (*  Norma (x -> 1, ()) *)
  let res = compose f g x in 
  (* ex ret_f ret_g; G(emp, ret_g); F(ret_g, ret_f); Norm(emp, ret_f) *)
  (* ex ret_f ret_g; 
    Norm(x->1, ()); req x->z; Norm(x->z * 2, x);  ~~~>  Norm(x->2, x);    // g 
    Norm(x->2, x);  req x->z1; Norm(x->z +1, x); ~~~>  Norm(x->3, x); 
    G(emp, ret_g); F(ret_g, ret_f); Norm(emp, ret_f) *)

  print_endline (string_of_int !res)