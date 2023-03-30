effect Exchange: int -> int


let exchange () 
(*@  
   ex old;
   Exchange(emp, 5, old);
   Norm(emp, old)
@*)
= let res = perform (Exchange 5) in 
  res 

let exchange_hanlder (y:int ref)
(*@  
   ex old; 
   req y -> old; 
   Norm(y -> 5, old)
@*)
= match exchange () with 
  | v -> v 
  | effect (Exchange n) k -> 
    let old = !y in 
    y := n; 
    continue k old

let main ()
(*@  
   Norm(x -> 5, 11)
@*)
= 
  let x = ref 11 in 
  let res = exchange_hanlder x in 
  print_endline (string_of_int res);
  res
