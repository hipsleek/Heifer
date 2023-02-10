effect Exchange: int -> int

let i = Sys.opaque_identity (ref 11) 

let test () 
(*@ req true
  ensure Exchange(5) (\ x ->
                requires emp
                ensures  Exchange(10) \ y ->
				       req emp
					   ensures Norm /\ res=x+y) @*)
= let res = perform (Exchange 5) in 
  let res1= perform (Exchange 10) in
  res+res1

let main
(*@ req i->v
 ens i->5 /\ res=v+1@*)
= 
  match test () with 
  | v -> v print_string ("Normal Rtn:" ^ string_of_int v ^ "\n")
   (*Norm -> \ r ->
            req ?
			ens post
      *)
  | effect (Exchange x) k -> 
    let oldv = !i in 
    i := x; 
    continue k oldv
	(* Exchange(v) k ->
      req i-> n
			ens 
      i-> v ; k n *)
