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

let test1 ()
(*@ 
  Write(emp, 10, x2); 
  ex x3; 
  Read(emp, x3); 
  Norm(emp, x3)
@*)
= 
  write 10;
  read ()

let test ()
(*@ 
  ex x1; 
  Read(emp, x1); 
  ex x2; 
  Write(emp, (x1+1), x2); 
  ex x3; 
  Read(emp, x3); 
  Norm(emp, x3)
@*)
= 
  let x = read () in 
  let y = x +1 in 
  write y;
  read () 

let handler () 
(*@ 
  ex i; 
  Norm(i->1,  1)
@*)
= let i = Sys.opaque_identity (ref 0) in 
  match test () with 
  | v -> !i
  | effect Read k -> (continue k (!i)) 
  | effect (Write x) k -> i := x; (continue k ())



let handler1 () 
(*@ 
  ex i; 
  Norm(i->10,  10)
@*)
= let i = Sys.opaque_identity (ref 0) in 
  match test1 () with 
  | v -> !i
  | effect Read k -> (continue k (!i)) 
  | effect (Write x) k -> i := x; (continue k ())

