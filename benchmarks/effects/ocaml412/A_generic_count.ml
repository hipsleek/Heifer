(* Generic counting example based on Hillerström et al. (2020) https://arxiv.org/abs/2007.00605 *)


effect Branch : bool

type point = int -> bool

let xor (p:bool) (q:bool): bool
(*@ req true; Norm(emp, p) @*) 
= (p && q)
(* xor(p, q): req true; (res = p&&q, Norm(res)) *)

let rec xor_predicate (n:int): bool
(* xor_predicate$(n, p, res):
  req n=0; res=false
  req n=1; p$(1, r); ens res=r
  req n>1; p$(n, r1); xor_predicate$(n-1, p, r2); ens res= r1 && r2 *)
= match n with
  | 0 -> false
  | 1 -> perform Branch
  | n ->
    let r1 = perform Branch in
    let r2 = xor_predicate (n-1) in
    xor r1 r2




let main counter n =
  (* main (counter, n, res) :
     ex z; req counter->z /\ n>0; (counter -> z + 2^(n+1)-2 /\ res=1, Norm (1)) *)
  match (xor_predicate n) with
  (* match_with (xor_predicate n, res) : (counter -> z + 2^(n+1)-2 /\ res=1, Norm (1)) *)
  | x -> if x then 1 else 0
  | exception e -> raise e
  | effect Branch k ->
    counter := !counter + 1;            (* increase the counter *)
    let tt = continue (Obj.clone_continuation k) true in
    counter := !counter + 1;            (* increase the counter *)
    let ff = continue k false in
    tt + ff


let test () 
(*@ req true; Norm(counter->6, 1) @*) 
= let counter = ref 0 in 
  main counter 3
  (*Printf.printf "Res:%d\n" solutions;
  Printf.printf "Counter:%d\n" !counter*) 