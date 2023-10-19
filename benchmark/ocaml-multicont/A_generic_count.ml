(* Generic counting example based on Hillerström et al. (2020) https://arxiv.org/abs/2007.00605 *)

open Effect.Deep
open Multicont.Deep

type _ Effect.t += Branch : bool Effect.t

type point = int -> bool

let xor : bool -> bool -> bool
(*@ xor(p, q): ex p, q; req true; ens res = p&&q @*)
  = fun p q -> (p && q)

let rec xor_predicate : int -> point -> bool
(*@ xor_predicate$(n, p, res): 
  req n=0; res=false
  req n=1; p$(1, r); ens res=r
  req n>1; xor_predicate$(n-1, p, r1); p$(n, r2); ens res= r1 && r2 @*)
  = fun n p ->
  match n with 
  | 0 -> false
  | 1 -> p 1 
  | n -> xor (xor_predicate (n-1) p) (p n)

let toss_twice () = 
  (*@ toss_twice(res): xor_predicate$(1, p, r1); p$(2, r2); (res=r1&&r2, Norm(res))  @*)
  (*@ toss_twice(res): p$(1, r1); p$(2, r2); (res=r1&&r2, Norm(res))  @*)
  (*@ toss_twice(res): Branch(r1); Branch(r2); (res=r1&&r2, Norm(res))  @*)
  (xor_predicate 1) (fun _ -> Effect.perform Branch) 

let _ =
  (*@ (counter -> 2^(n+1)-2 /\ solutions=1, Norm (())) @*)
  let counter = ref 0 in 
  let solutions = 
    match_with toss_twice () (* n *)
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
      | _ -> None) } in
  Printf.printf "Res:%d\n" solutions;
  Printf.printf "Counter:%d\n" !counter

