(* Generic counting example based on Hillerström et al. (2020) https://arxiv.org/abs/2007.00605 *)

open Effect.Deep
open Multicont.Deep

type _ Effect.t += Branch : bool Effect.t

let counter = ref 0

type point = int -> bool

let xor : bool -> bool -> bool
(*@ xor(p, q): req true; (res = p&&q, Norm(res)) @*)
  = fun p q -> (p && q)

let rec xor_predicate : int -> point -> bool
(*@ xor_predicate$(n, p, res): 
  req n=0; res=false
  req n=1; p$(1, r); ens res=r
  req n>1; p$(n, r1); xor_predicate$(n-1, p, r2); ens res= r1 && r2 @*)
  = fun n p ->
  match n with 
  | 0 -> false
  | 1 -> p 1 
  | n -> 
    let r1 = p n in 
    Printf.printf "(p %d):%d\n" n !counter ; 
    let r2 = (xor_predicate (n-1) p) in 
    Printf.printf "xor_predicate %d:%d\n" ((n-1)) !counter ;
    xor r1 r2

let main counter n =
  (*@ main (counter, n, res) : 
     ex z; req counter->z /\ n>0; (counter -> z + 2^(n+1)-2 /\ res=1, Norm (1)) @*)
    match_with (xor_predicate n)  (fun _ -> Effect.perform Branch) 
    (*@ match_with (xor_predicate n, res) : (counter -> z + 2^(n+1)-2 /\ res=1, Norm (1)) @*)
    { retc = (fun x -> if x then 1 else 0)
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | Branch ->
        Some (fun (k : (a, _) continuation) ->
           let r = promote k in
           counter := !counter + 1;            (* increase the counter *)
           let tt = resume r true in
           counter := !counter + 1;            (* increase the counter *)
           let ff = resume r false in
           tt + ff)
      | _ -> None) }

let _ = 
  let solutions = main counter 3 in 
  Printf.printf "Res:%d\n" solutions;
  Printf.printf "Counter:%d\n" !counter  