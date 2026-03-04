effect E : int 
effect E1 : string 

let foo () 
(*@ 
   ex ret; 
   E1(emp, ret);
   Norm(emp, ret)
@*)
= perform E1

let bar () 
(*@ 
   ex ret; 
   E1(emp, ret);
   Norm(emp, ret)
@*)
=
  match foo () with 
  | x -> x 
  | effect E k -> assert false

let baz () 
(*@ 
   Norm(emp, 1)
@*)
=
  match bar () with 
  | x -> x 
  | effect E1 k -> continue k 1

