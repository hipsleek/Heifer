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
   ex ret; 
   Read(emp, ret);
   Norm(emp, ret)
@*)
= let x = read () in 
  let x' = x + 1 in 
  write x';
  read () 

let handler1 () 
(*@ 
   ex ret; 
   Read(emp, ret);
   Norm(emp, ret)
@*)
= 
  match client () with
  | v -> ()
  | effect (Write x) k -> i := x; (continue k ())

let handler2  ()
(*@ 
   ex ret; 
   Read(emp, ret);
   Norm(emp, ret)
@*)
=
  match handler1 () with
  | v -> ()
  | effect Read k -> (continue k (!i))
