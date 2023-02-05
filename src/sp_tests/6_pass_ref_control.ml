effect Pass : int ref -> unit

let callee () 
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->0}.Pass(i).{i->i+2}.[i=3]) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform (Pass i);
  i := !i + 2;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 3)

let main 
(*@  requires (true, emp) @*)
(*@  ensures  (true, {i->0}.{i->i+1}.{i->i+2}.[i=3]) @*)
=
  match callee () with
  | v -> ()
  | effect (Pass r) k ->  r := !r + 1;
    (continue k ()); 

