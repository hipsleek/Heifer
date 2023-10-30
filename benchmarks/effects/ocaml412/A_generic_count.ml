(* Generic counting example based on Hillerström et al. (2020) https://arxiv.org/abs/2007.00605 *)


effect Branch : bool

type point = int -> bool

let xor (p:bool) (q:bool): bool
(*@ ex res; Norm(res=p&&q, res) @*) 
= (p && q)

let rec xor_predicate (n:int): bool
(*@  req n=0; Norm(res=0) 
  \/ req n=1; Branch(emp, res)
  \/ ex r1; req n>1; Branch(emp, r); ex r2; xor_predicate(n-1, r2); Norm(res = r1 && r2)  @*) 
= match n with
  | 0 -> false
  | 1 -> perform Branch
  | n ->
    let r1 = perform Branch in
    let r2 = xor_predicate (n-1) in
    xor r1 r2

let main counter n 
  (*@ ex z; req counter->z /\ n>0; Norm(counter -> z+ 2^(n+1) -2, 1) @*)
= match (xor_predicate n) with
  (*@ ex z; req counter->z /\ n>0; Norm(counter -> z+ 2^(n+1) -2, 1) @*)
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
  main counter 3
  (*Printf.printf "Res:%d\n" solutions;
  Printf.printf "Counter:%d\n" !counter*) 