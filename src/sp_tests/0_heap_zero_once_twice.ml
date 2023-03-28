effect Zero : unit

let test () 
(*@ ex i ret z u;
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


let main_aux ()
(*@ ex x ret z u;
   Norm(i->2, ())
@*)
=
  match callee2 () with
  | v -> print_string ("Done 0 \n"); perform Done 
  | effect Zero k -> ()
  | effect Once k ->
    (continue k ()); 
  | effect Twice k ->
    (continue (Obj.clone_continuation k) ()); (continue k ())


let main ()
(*@ 
   Norm(emp, ())
@*)
= 
  match main_aux () with 
  | x ->  ()
  | effect Done k -> print_string ("Done here\n"); continue k ()
