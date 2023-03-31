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
  Write(emp, (x1+1), x2); 
  ex x3; 
  Read(emp, x3); 
  Norm(emp, x3)
@*)
= let x = read () in 
  let x' = x + 1 in 
  write x';
  read () 

let handler1 () 
(*@ 
  ex ret ret1; 
  Read(emp, ret); 
  Read(i->ret+1,  ret1)
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
