effect Zero : int 

let rec aux li =
  match li with
  | [] -> 1 
  | x :: xs -> 
    if x == 0 then perform Zero 
    else x * aux xs 

let times2 li = 
  match aux li with 
  | v -> v 
  | effect Zero k -> 0 

(*  
aux(li, res) =  
     ens[res] li = [] /\ res=1
  \/ ens li = x :: xs /\ x =0 ; Zero(res)
  \/ ens li = x :: xs /\ x!=0 ; aux(xs, r); ens[res] res = x * r 
*)

(*  
times2(li, res) =  
     ens[res] li = [] /\ res=1
  \/ ens[res] li = x :: xs /\ x =0 ; res=0
  \/ ens li = x :: xs /\ x!=0 ; aux(xs, r); ens[res] res = x * r 

== times(li, res)
*)