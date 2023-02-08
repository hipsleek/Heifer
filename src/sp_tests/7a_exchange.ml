effect Exchange: int -> int

let i = Sys.opaque_identity (ref 11) 

let test () 
(*@  requires (true, emp)   @*)
(*@  ensures  (true, [exist a.i->a].Exchange(5), ret = Exchange(5)?) @*)
// req true
// ensure Exchange(5) (\ x ->
                requires emp
                ensures  Exchange(10) \ y ->
				       req emp
					   ensures Norm /\ res=x+y)
= 
  (* requires exist a. !i->a *)
  let res = perform (Exchange 5) in 
  let res1= perform (Exchange 10) in
  res+res1

let main
(*@  requires (true, emp)   @*)
(*@  ensures  (true, [a.!i->a].{i->5}.Normal(11)) @*)
 req i->v
 ens i->5 /\ res=v+1
= 
  match test () with 
  | v -> v print_string ("Normal Rtn:" ^ string_of_int v ^ "\n")
  | effect (Exchange x) k -> 
    let oldv = !i in 
    i := x; 

    continue k oldv