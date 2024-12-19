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


let test ()
(*@ 
  ex x1; 
  Read(emp, x1); 
  ex x2; 
  Write(emp, (x1+1), x2); 
  ex x3; 
  Read(emp, x3); 
  ex x4; 
  Write(emp, (x3+1), x4); 
  ex x5; 
  Read(emp, x5); 
  Norm(emp, x5)
@*)
= 
  let x = read () in 
  write (x+1);
  let z = read () in 
  write (z+1);
  read ()

let handler () 
(*@ 
  ex i; 
  Norm(i->2,  2)
@*)
= let i = Sys.opaque_identity (ref 0) in 
  match test () with 
  | v -> !i
  | effect Read k -> (continue k (!i)) 
  | effect (Write x) k -> i := x; (continue k ())

