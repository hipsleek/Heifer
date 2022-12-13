effect Twice : unit
effect Once : unit

let callee1 () 
(*@ requires emp  @*)
(*@ ensures Once(i:=old(i)+1).[i=1] @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Once;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

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
  match callee2 () with
  | v -> ()
  | effect Once k ->
    (continue k ()); 
  | effect Twice k ->
    (continue (Obj.clone_continuation k) ()); (continue k ()); 

