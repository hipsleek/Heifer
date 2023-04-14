effect E : int 
effect F : string 

let foo () 
(*@ 
   ex ret; 
   F(emp, ret);
   Norm(emp, ret)
@*)
= perform F

let bar () 
(*@ 
   ex ret; 
   F(emp, ret);
   Norm(emp, ret)
@*)
=
  match foo () with 
  | x -> x 
  | effect E k -> (failwith "impossible")

let baz () 
(*@ 
   Norm(emp, 1)
@*)
=
  match bar () with 
  | x -> x 
  | effect F k -> continue k 1

