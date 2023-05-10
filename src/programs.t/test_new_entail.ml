
effect Eff : unit 

(* basic *)

let test10_true ()  (*@ Norm(emp, 0) @*) = 0
(* implicit normal stage *)

let test6_true ()  (*@ Norm(emp, 0) @*) =
  let j = 0 in
  j (* intermediate bindings don't matter? *)

let test7_false ()  (*@ Norm(emp, j) @*) =
  let j = 0 in
  j (* j is not a param *)

let test8_false ()  (*@ Norm(emp, k) @*) =
  let j = 0 in
  j (* k is not a param *)

let test9_true ()  (*@ ex j; Norm(emp, j) @*) =
  let j = 0 in
  j (* existential j should work *)

let test4_true ()  (*@ ex i; Norm(i->0, i) @*) =
  let i = ref 0 in 
  i (* heap *)

let test5_true ()  (*@ ex i; Norm(i->0, 1) @*) =
  let i = ref 0 in 
  !i + 1 (* heap value *)

let test6_true ()  (*@ ex i; Norm(i->1, 1) @*) =
  let i = ref 0 in 
  i := !i + 1; (* assignment *)
  !i

let test11_true ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret

let test12_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  1

let test19_true ()  (*@ ex r; Eff(emp, r) @*) =
  let ret = perform Eff in
  1

let test21_true ()  
(*@ ex i ret;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 1;
  ret

let test0_true ()  
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

let test1_false ()  
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

let test2_false ()  
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

let test3_false ()  
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

let test13_true ()  
(*@ ex a b;
   Norm(a->0 * b->1, 1)
@*)
= 
  let i = ref 0 in 
  let j = ref 1 in 
  1

let test18_true ()  
(*@ ex a b;
   Norm(a->1+1 * b->0, 1)
@*)
= 
  let i = ref 0 in 
  let j = ref 2 in 
  1

let test20_true ()
(*@ ex b;
   req i->1;
   Norm(i->1 * b->2, 1)
@*)
=
  assert (i-->1);
  let j = ref 2 in 
  1

let test21_true ()
(*@ ex b;
   req i->1;
   Norm(i->1 * b->2, 1)
@*)
=
  assert (!i = 1);
  let j = ref 2 in 
  assert (!j = 2);
  1

let test22_true ()
(*@ ex i a;
   Norm(i->a, ())
@*)
=
  let j = ref 2 in 
  let z = !j in
  assert (!j = z)

let test14_false ()  
(*@ ex a b;
   Norm(a->1 * b->1, 1)
@*)
= 
  let i = ref 0 in 
  let j = ref 1 in 
  1

let test15_true ()  
(*@
   req a->1;
   Norm(a->1, 1)
@*)
= 
  assert (a-->1);
  1

let test16_false ()  
(*@ ex a;
   req a->1;
   Norm(a->1, 1)
@*)
= 
  let i = ref 0 in 
  1

let test17_true ()  
(*@ ex b;
   req a->1;
   Norm(a->1 * b->0, 1)
@*)
= 
  assert (a-->1);
  let i = ref 0 in 
  1

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