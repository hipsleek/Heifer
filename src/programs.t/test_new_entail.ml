
effect Eff : unit 

(* basic *)

let test10_t ()  (*@ Norm(emp, 0) @*) = 0
(* implicit normal stage *)

let test6_t ()  (*@ Norm(emp, 0) @*) =
  let j = 0 in
  j (* intermediate bindings don't matter? *)

let test7_f ()  (*@ Norm(emp, j) @*) =
  let j = 0 in
  j (* j is not a param *)

let test8_f ()  (*@ Norm(emp, k) @*) =
  let j = 0 in
  j (* k is not a param *)

let test9_t ()  (*@ ex j; Norm(emp, j) @*) =
  let j = 0 in
  j (* existential j should work *)

let test4_t ()  (*@ ex i; Norm(i->0, i) @*) =
  let i = ref 0 in 
  i (* heap *)

let test5_t ()  (*@ ex i; Norm(i->0, 1) @*) =
  let i = ref 0 in 
  !i + 1 (* heap value *)

let test6_t ()  (*@ ex i; Norm(i->1, 1) @*) =
  let i = ref 0 in 
  i := !i + 1; (* assignment *)
  !i

let test11_t ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret

let test_t ()  
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

let test1_f ()  
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

let test2_f ()  
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

let test3_f ()  
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