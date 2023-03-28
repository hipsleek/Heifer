effect Zero : unit

let test () 
(*@ ex x ret z u;
   Norm(i->0, ());
   Zero(emp, ret);
   req i->z; Norm(i->z+1, ());
   req i->1;
   Norm(i->1, ret)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Zero in 
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1);
  ret

let hello () 
(*@ ex v; req x->1 * y->2; Norm(z->3, w); Eff(z->3, v, u, r) @*)
=
  let i = Sys.opaque_identity (ref 0) in 
  perform Zero;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)
