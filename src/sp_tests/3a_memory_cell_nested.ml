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
  ex x1; 
  Read(emp, x1); 
  ex x2; 
  Write(emp, 10, x2); 
  Norm(emp, x2)
@*)
= read ();
  write 10

let handler1 i  
(*@ 
  ex ret ret1 z; 
  Read(emp, ret); 
  req i-> z; 
  Norm(i->10,  ())
@*)
= 
  match client () with
  | v -> ()
  | effect (Write x) k -> i := x; (continue k ())


let handler2  ()
(*@ 
  ex i; 
  Norm(i->10,  10)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  match handler1 i with
  | v -> v (*print_string (string_of_int !i) *)
  | effect Read k -> (continue k (!i))


