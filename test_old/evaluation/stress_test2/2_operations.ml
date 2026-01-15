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
ex x1; Read(emp, x1); ex r1; Write(emp, (x1+1), r1);

  ex x3000; 
  Read(emp, x3000); 
  Norm(emp, x3000)
@*)
= 
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  read () 




