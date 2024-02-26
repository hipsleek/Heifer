effect Flip : bool

let rec tossNtimeTail n 
(*@ req n>=1; Flip(n=1, res)  \/ 
    req n>=1; ex r1; Flip(emp, r1); ex r2; tossNtimeTail(n-1, r2); Norm(n>1, r1&&r2)  @*)
= if n==1 then 
    perform Flip
  else 
    let r1 = perform Flip in 
    let r2 = tossNtimeTail (n-1) 
    in r1 && r2

(* try ex r; req n>=0; tossNtimeTail(n,r) #  Norm((acc&&r)=false,0) \/ Norm((acc&&r)=true,1) catch 
  =   ex w final; req i->w; Norm (i->w+(2^(n+1) -2) /\ (final=1/\acc=true \/ final=0/\acc=false), final)  *) 

let tossHandlerTail counter n 
(*@ ex w; req i->w; Norm (i->w+((2^(n+1)) -2) ,1) @*)
= match tossNtimeTail n with 

  (* try-catch lemma defined here *)
  (*@ try ex r; req n>=0; tossNtimeTail(n,r) 
      # Norm((acc&&r)=false,0) \/  Norm((acc&&r)=true,1) catch 
  =  ex w1 final1; req i->w1; Norm (i->w1+((2^(n+1)) -2) /\  final1=1/\acc=true , final1) 
  \/ ex w2 final2; req i->w2; Norm (i->w2+((2^(n+1)) -2) /\  final2=0/\acc=false, final2)  @*) 
  
  | x -> if x 
         then 1 
         else 0     

  | effect Flip k ->
      counter := !counter + 1;            (* increase the counter *)
      let res1 = continue (Obj.clone_continuation k) true in         (* resume with true     *)
      counter := !counter + 1;            (* increase the counter *)
      let res2 = continue k false in      (* resume with false    *)
      res1 + res2                         (* gather the results   *)

