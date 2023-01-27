effect Twice : unit
effect Once : unit
effect Zero : unit

let callee0 () 
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->0}.Zero.{i->i}.[i=1]) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Zero;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

let callee1 () 
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->0}.Once.{i->i}.[i=1]) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Once;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

(* 1. ASSERTION IN THE SPEC *)
(* 2. MUILTISHOT GENERALISE *)

let callee2 () 
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->0}.Twice.{i->i}.[i=1]) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Twice;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)
