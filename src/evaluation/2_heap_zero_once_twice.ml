effect Zero : int 
effect Once : int 
effect Twice : int 

let test () 
(*@ ex i ret;
   Twice(i->0, ret);
   req i-> 0; 
   Norm(i->1, ret)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Twice in 
  i := !i + 1;
  assert (!i = 1);
  ret

let main_false ()
(*@ ex i;
   Norm(i->2, 2)
@*)
=
  match test () with
  | v -> v
  | effect Zero k -> 100
  | effect Once k ->
    (continue k 1); 
  | effect Twice k ->
    let _ = (continue (Obj.clone_continuation k) 1) in (continue k 2)

