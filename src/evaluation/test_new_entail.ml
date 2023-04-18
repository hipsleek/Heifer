
effect Eff : unit 

let test ()  
(*@ ex i ;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 1;
  ret

let test1 ()  
(*@ ex i ;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 1;
  !i (* wrong *)

let test2 ()  
(*@ ex i ;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  (* state unchanged *)
  ret

let test3 ()  
(*@ ex i ;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 2; (* wrong stae *)
  ret

(* the inferred post state of this function is weird, probably because the existentials are gone *)

(*
let main_aux ()
   (*@ ex i;
      Norm(i->2, ())
   @*)
   = (match test () with
     | v -> v
     | effect Eff k ->
       (continue (Obj.clone_continuation k) ());
       (continue k ())
     );
*)