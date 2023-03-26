effect Twice : unit
effect Once : unit
effect Zero : unit
effect Done : unit

let callee0 () 
(*@ ex x ret z u;
   Zero(i->0, ret);
   req i->0; Norm(i->1, ());
   Norm(i->1, ())
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  perform Zero;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

let callee1 () 
(*@ ex x ret z u;
   Norm(i->0, ());
   Once(emp, ret);
   req i->z; Norm(i->z+1, ());
   req i->1;
   Norm(i->1, ())
@*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Once;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

(* 1. ASSERTION IN THE SPEC *)
(* 2. MUILTISHOT GENERALISE *)

let callee2 () 
(*@ ex x ret z u;
   Norm(i->0, ());
   Twice(emp, ret);
   req i->z; Norm(i->z+1, ());
   req i->1;
   Norm(i->1, ())
@*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Twice;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

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


let main 
(*@ 
   Norm(emp, ())
@*)
= 
  match main_aux () with 
  | x ->  ()
  | effect Done k -> print_string ("Done here\n"); continue k ()
