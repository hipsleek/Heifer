effect Read : int 
effect Write : int -> unit 

(* let (i: int ref) = Sys.opaque_identity (ref 0) *)

let read () 
(*@ 
   ex ret; 
   Read(emp, ret);
   Norm(emp, ret)
@*)
= perform Read

let write n 
(*@ 
   ex ret; 
   Write(emp, n,  ret);
   Norm(emp, ret)
@*)
= perform (Write n)


let read_handler ()
(*@ 
  ex i; 
  Norm(i->0,  0)
@*)
= let i = Sys.opaque_identity (ref 0) in 
  match read ();read () with 
  | v -> v
  | effect Read k -> (continue k (!i)) 



let write_handler  ()
(*@ 
  ex i; 
  Norm(i->10,  10)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  match write 10; write 20 with
  | v -> !i (*print_string (string_of_int !i) *)
  | effect (Write x) k -> i := x; (continue k ())

