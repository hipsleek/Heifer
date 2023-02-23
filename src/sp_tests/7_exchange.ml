effect Exchange: int -> int

let i = Sys.opaque_identity (ref 11) 

let test () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Exchange(5), Exchange(5)?) @*)
= 
  (* requires exist a. !i->a *)
  let res = perform (Exchange 5) in 
  let res1 = perform (Exchange 10) in 

  res

let main
(*@  requires (true, emp)   @*)
(*@  ensures  (true, [a.!i->a].{i->5}.Normal(11), ()) @*)
= 
  match test () with 
  | v -> v print_string ("Normal Rtn:" ^ string_of_int v ^ "\n")
  | effect (Exchange x) k -> 
    let oldv = !i in 
    i := x; 

    continue k oldv