

let test19 ()  (*@ ex r; Eff(emp, r) @*) =
  let ret = perform Eff in
  ret
(* this is the only correct implementation. note that the spec is implicitly completed with ... Norm(emp, r), the return value of the previous stage. *)

let test27 ()  (*@ ex r; Eff(emp, r); ex r1; Norm(emp, r1) @*) =
  let ret = perform Eff in
  1
(* if we explicitly give a Norm, the return value of perform and the function can differ *)

let test25 ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret
(* this can be proved in why3 due to it leveraging type information - since ret is of type unit, its value must be (). *)

(* let test12_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  1 *)
(* this fails with a type error in why3, as it should *)

let test21 ()
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

let test0 ()
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

let two_locations ()
(*@ ex i j z1 z2 ret;
   E(i->0 * j->0, ret);
   req i->z1 * j->z2;
   Norm(i->z1+1*j->z2+1, ret)
@*)
= let i = ref 0 in
  let j = ref 0 in
  let ret = perform E in
  i := !i + 1;
  j := !j + 1;
  ret
