effect Inc : int -> int 




let rec sumEff n 
(*@ req n>0; ens n=1; Norm(emp, 1) \/  
    req n>0; ens n>1; ex r1 res; 
    Inc(emp, n, r1); ex r2; 
    sumEff(n-1,r2); 
    Norm(res=r1+r2, res) @*)
= if n == 1 then 1
  else 
    let r = perform (Inc n) in 
    r + sumEff(n-1)

(*
  TRY ex res; sumEff(n,res) # ex r' acc'; Norm(acc'=acc+res, acc') CATCH  === 
  ex r w; req i->w; Norm (i->w+(n*.(n-1)/2), n+acc)
*) 

let handler n 
(*@ req n>0; ex i; Norm(i->(n*.(n-1)/2) , n) @*)
= let i = ref 0 in 
  match sumEff n with 
  (*@ try ex res; sumEff(n,res) #  ex r' acc'; Norm(acc'=acc+res, acc')  catch 
  =
  ex r w; req i->w; Norm (i->w+(n*.(n-1)/2), n+acc)  @*) 
  | v ->  v
  | effect (Inc v) k -> i := !i + v -1; continue k 1

(* ASK DARIUS: changing this res value the entailment still succeed *)
let test () 
(*@ ex i res; Norm(i-> 10 /\ res=6, res) @*)
= handler 5
