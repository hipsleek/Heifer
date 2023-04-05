effect Eff : unit 

let test i 
(*@ ex i ret;
   Eff(i->0, ret);
   ex z ;
   req i-> z; 
   Norm(i->z+1, ())
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 1;
  let ret = perform Eff in 
  i := !i + 1;
  ret

let main_aux ()
(*@ ex i;
   Norm(i->1, 1)
@*)
=
  (match test () with
  | v -> v 
  | effect Eff k ->
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue (Obj.clone_continuation k) ());
    (continue k ())
  );
  print_endline (string_of_int !i)

