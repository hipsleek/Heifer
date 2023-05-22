
effect Eff : unit 

(* basic *)

let test10_true ()
  (*@ Norm(emp, 0) @*) =
  0
(* implicit normal stage *)

let test6_true ()
  (*@ Norm(emp, 0) @*) =
  let j = 0 in
  j
(* intermediate bindings don't matter? *)

let test7_false ()
  (*@ Norm(emp, j) @*) =
  let j = 0 in
  j
(* j is not a param *)

let test8_false ()
  (*@ Norm(emp, k) @*) =
  let j = 0 in
  j
(* k is not a param *)

let test9_true ()
  (*@ ex r; Norm(emp, r) @*) =
  let j = 0 in
  j
(* existential return value *)

let test4_true ()
  (*@ ex i; Norm(i->0, i) @*) =
  let i = ref 0 in 
  i
(* new heap location, hence existential *)

let test5_true ()  (*@ ex i; Norm(i->0, 1) @*) =
  let i = ref 0 in 
  !i + 1
(* heap read *)

let test6_true ()  (*@ ex i; Norm(i->1, 1) @*) =
  let i = ref 0 in 
  i := !i + 1;
  !i
(* heap update *)

let test23_false ()  (*@ ex i; Norm(i->1, 1) @*) =
  let i = ref 0 in 
  i := !i + 2;
  !i
(* wrong value *)

let test19_true ()  (*@ ex r; Eff(emp, r) @*) =
  let ret = perform Eff in
  ret
(* this is the only correct implementation. note that the spec is implicitly completed with ... Norm(emp, r), the return value of the previous stage. *)

let test27_true ()  (*@ ex r; Eff(emp, r); ex r1; Norm(emp, r1) @*) =
  let ret = perform Eff in
  1
(* if we explicitly give a Norm, the return value of perform and the function can differ *)

let test25_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret
(* we can't justify that whatever Eff returns is unit *)

let test12_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  1
(* this fails for the same reason. the return value is not checked *)

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
(*@ ex i z ret;
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
(*@ ex i z ret;
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
(*@ ex i z ret;
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
(*@ ex i z ret;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 2; (* wrong state *)
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

let f1 () (*@ Norm(emp, 1) @*) = 1

let test24_true ()  (*@ Norm(emp, 1) @*) =
  let ret = f1 () in
  ret

let fa a (*@ req a=1/\emp; Norm(emp, 2) @*) = a + 1

let test26_true ()  (*@ Norm(emp, 2) @*) =
  let ret = fa 1 in
  ret

let two_locations_true () 
(*@ ex i j z1 z2 ret;
   E(i->0 * j->0, ret);
   req i->z1 * j->z2; 
   Norm(i->z1+1*j->z2+1, ret)
@*)
= let i = ref 0 in 
  let j = ref 0 in 
  let ret = perform (E) in 
  i := !i + 1;
  j := !j + 1;
  ret

let if_disj_true b
(*@ Norm(emp, 1) \/ Norm(emp, 2)
@*)
= if b then 1 else 2
