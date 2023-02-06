effect Exchange: int -> int

let i = Sys.opaque_identity (ref 11) 

let test () 
(*@  requires (true, emp)   @*)
(*@  ensures  (true, Exchange (5)) @*)
= 
  print_string ("previous value of i = " ^ string_of_int !i ^ "\n");
  let res = perform (Exchange 5) in 
  print_string ("res =  " ^ string_of_int res ^ "\n");
  print_string ("updated value of i = " ^ string_of_int !i ^ "\n")

let main
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->5}) @*)
= 
  match test () with 
  | v -> v
  | effect (Exchange x) k -> 
    let oldv = !i in 
    i := x; 
    continue k oldv