effect Exchange: int -> int

let i = Sys.opaque_identity (ref 11) 

let test ()
  (*@  req emp   @*)
  (*@  ens Exchange(5) * Cont = (\ x ->
           req emp
           ens Exchange(8) * Cont = (\ x2 ->
             req emp
             ens res=x+x2 & Norm(res)
         )
      )
   @*)
  = let res = perform (Exchange 5) in
    let res2 = perform (Exchange 8) i
    res+res2

let main
  (*req i-> init
  ens i-> 8 /\ Norm(res) /\ res=init+5
            /\ Cont = \ _ -> req false ens true // default*)
  = match test () with
    | v -> print_string ("Normal Rtn:" ^ string_of_int v ^ "\n");
          v + 1
    (*@ Norm(v) =
       req emp
       ens Norm(res) /\ res=v+1
    @*)
    | effect (Exchange x) k ->
      let oldv = !i in
      i := x;
      let r1 = (continue (Obj.clone_continuation k) oldv) in
      let r2 = (continue k oldv) in
      print_string ("r1 = " ^ string_of_int r1 ^ "\nr2 = " ^ string_of_int r2^ "\n");
      r1 + r2

    (*@ Exchange(x) k =
       req i->oldv
       ens i->x /\ Norm(res) /\ res=k oldv
    @*)