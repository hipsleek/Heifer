effect Twice : unit
effect Once : unit

let callee1 () 
(*@ requires emp  @*)
(*@ ensures Once.(i:=old(i)+1).[i=1] @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Once;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

(* 1. ASSERTION IN THE SPEC *)
(* 2. MUILTISHOT GENERALISE *)


let callee2 () 
(*@ requires emp  @*)
(*@ ensures Twice(i:=old(i)+1).[i=1] @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Twice;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

let main 
=
(*@ ensures Once.(i:=old(i)+1).[i=1] @*)
  match callee1 () with
  | v -> ()
  | effect Once k ->
    (continue k ()); 
  | effect Twice k ->
    (continue (Obj.clone_continuation k) ()); (continue k ()); 

(*      
For Once: (Once(i:=old(i)+1).[i=1])
     currenct effects       continuation k 
      Once                i:=old(i)+1 . [i=1]'
  
For TWICE: (TWICE(i:=old(i)+1).[i=1])
     currenct effects       continuation k 
      TWICE                i:=old(i)+1 . [i=1].    i:=old(i)+1 . [i=1]

*)

