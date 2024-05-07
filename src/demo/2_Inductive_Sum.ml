effect Inc : int -> int 

let rec sumEff n 
(*@ req n>=0; Norm(n=0, 0) \/  
    req n>=0; 
    ex r1; Inc(emp, n, r1); 
    ex r2; sumEff(n-1,r2); 
    Norm(n>0 /\ res=r1+r2, res) @*)
= if n == 0 then 0
  else 
    let r = perform (Inc n) in 
    r + sumEff(n-1)


let handler n 
(*@ req n>=0; ex i; Norm(i->(n*.(n+1)/2) , n) @*)
= let i = ref 0 in 
  match sumEff n with 
  (* try-catch lemma defined here *)
  (*@   try ex r; req n>=0; sumEff(n,r) # Norm(emp,acc+r) catch 
     =  ex w; req i->w; Norm (i->w+(n*.(n+1)/2), n+acc)  @*) 
  | v ->  v
  | effect (Inc v) k -> 
    i := !i + v; 
    continue k 1


    
(*
let test1 () 
(*@ ex i; Norm(i-> 10 /\ res=5, res) @*)
= handler 5


let test2 () 
(*@ ex i; Norm(i-> 45 /\ res=10, res) @*)
= handler 10


let test3 () 
(*@ ex i; Norm(i-> 4950 /\ res=100, res) @*)
= handler 100
*)