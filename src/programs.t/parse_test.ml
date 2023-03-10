effect Zero : unit

let test () 
(*@ ex x ret z u;
   Norm(x->0, ());
   req y->1;
   Label(emp, ret);
   req x->z; Norm(x->z+1, ());
   req x->1;
   Norm(x->1, ())
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  perform Zero;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

let hello () 
(*@ ex v; req x->1 * y->2; Norm(z->3, w); Eff(z->3, v, u, r) @*)
=
  let i = Sys.opaque_identity (ref 0) in 
  perform Zero;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)
