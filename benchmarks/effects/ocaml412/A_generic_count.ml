(* Generic counting example based on Hillerström et al. (2020) https://arxiv.org/abs/2007.00605 *)


effect Branch : bool

type point = int -> bool

let xor (p:bool) (q:bool): bool
(*@ Norm(res=p&&q) @*) 
= (p && q)

let rec xor_predicate (n:int): bool
(*@ req n>=0 ; Norm(n=0 /\ res=true) 
  \/ex r; req n>=0; Norm(n=1); Branch(emp, r); Norm(res=r)  
  \/ex r1; req n>=0; Branch(n>1, r1); ex r2; xor_predicate(n-1, r2); Norm(res = r1 && r2)
@*)
= if n==0 then true 
  else if n==1 then perform Branch
  else 
    let r1 = perform Branch in
    let r2 = xor_predicate (n-1) in
    xor r1 r2


let main counter n 
  (*@ ex z; req counter->z /\ n>=0; Norm(counter -> z+ (2^(n+1)) -2, 1) @*)
= match (xor_predicate n) with
  (*@ ex z; req counter->z; Norm(counter -> z+ (2^(n+1)) -2, true) @*)
  | x -> if x then 1 else 0
  | exception e -> raise e
  | effect Branch k ->
    counter := !counter + 1;            (* increase the counter *)
    let tt = continue (Obj.clone_continuation k) true in
    counter := !counter + 1;            (* increase the counter *)
    let ff = continue k false in
    tt + ff


let test () 
(*@ ex counter; Norm(counter->6, 1) @*) 
= let counter = ref 0 in 
  main counter 2
  (*Printf.printf "Res:%d\n" solutions;
  Printf.printf "Counter:%d\n" !counter*) 
