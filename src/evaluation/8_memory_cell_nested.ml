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

let client () 
(*@ 
  ex x2;
  Write(emp, 10, x2); 
  ex x3; 
  Read(emp, x3); 
  Norm(emp, x3)
@*)
= write 10;
  read () 
  

let handler1 i 
(*@ 
  ex z; 
  req i -> z;
  Read(i ->10, x3); 
  Norm(emp, x3)
@*)
= 
  match client () with
  | v -> v
  | effect (Write x) k -> i := x; (continue k ())


let handler2  ()
(*@ 
   ex i; 
   Norm(i->10, ())
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  match handler1 i with
  | v -> () (*print_string (string_of_int !i) *)
  | effect Read k -> (continue k (!i))


