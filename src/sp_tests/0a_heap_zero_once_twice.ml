effect Zero : int 
effect Once : int 
effect Twice : int 

let test () 
(*@ ex i ret;
   Zero(i->0, ret);
   req i-> -; 
   Norm(i->1, ret)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Once in 
  i := !i + 1;
  assert (!i = 1);
  ret

let main_aux ()
(*@ ex i;
   Norm(i->2, ())
@*)
=
  match test () with
  | v -> v
  | effect Zero k -> (-1)
  | effect Once k ->
    (continue k 1); 
  | effect Twice k ->
    let _ = (continue (Obj.clone_continuation k) 1) in (continue k 2)

