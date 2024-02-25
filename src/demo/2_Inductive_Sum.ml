effect Inc : int -> int 


(*
sumEff(n,res) = n=0 /\ res=n
  \/ n>0 /\ ex r; (emp, Inc(n,r)); 
     ex r2; (emp, sumEff(n-1,r2)); 
     (emp, Norm(r+r2))
*)

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


let handler n 
(*@ req n>0; ex i; Norm(i->(n*.(n-1)/2) , n) @*)
= let i = ref 0 in 
  match sumEff n with
  | v ->  v
  | effect (Inc v) k -> i := !i + v -1; continue k 1

(* ASK DARIUS: changing this res value the entailment still succeed *)
let test () 
(*@ ex i res; Norm(i-> 10 /\ res=6, res) @*)
= handler 5
