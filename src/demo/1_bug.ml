effect Read : int 
effect Write : int -> unit 
effect Exchange: int -> int


let read () 
(*@ ex ret; Read(emp, ret); Norm(emp, ret) @*)
= perform Read


let write n 
(*@ ex ret; Write(emp, n,  ret); Norm(emp, ret) @*)
= perform (Write n)


(* ASK DARIUS : the enatilment checking does not terminate *)
let test1 ()
(* ex r1; Read(emp, r1); 
    ex r2 r3; Write(r2=r1+1, (r2), r3); 
    ex r4; Read(emp, r4); 
    ex r5 r6; Write(r5=r4+1, (r5), r6); 
    ex r7; Read(emp, r7); Norm (res=r7, res)  @*)
= 
  let x = read () in 
  write (x+1);
  let z = read () in 
  write (z+1);
  read ()