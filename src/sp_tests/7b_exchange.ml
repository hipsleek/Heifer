effect Exchange: int -> int

let exchange (m:int)
(*@  
   ex ret;
   Exchange(emp, m, ret);
   Norm(emp, ret)
@*)
= perform (Exchange m)


let exc_hanlder (y:int ref) (new_v:int)
(*@  
   ex old_v; 
   req y -> old_v; 
   Norm(y -> new_v, old_v)
@*)
= match exchange new_v with 
  | v -> v 
  | effect (Exchange n) k -> 
    let old_v = !y in 
    y := n; 
    continue k old_v

(*



let main 
(*@  
  ex x;
  Norm(x -> 5, 11)
@*)
= 
  let x = ref 11 in 
  let res = exc_hanlder x 5 in 
  print_endline (string_of_int res);
  res
  *)
