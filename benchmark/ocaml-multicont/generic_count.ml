(* Generic counting example based on Hillerström et al. (2020) https://arxiv.org/abs/2007.00605 *)

open Effect.Deep

type _ Effect.t += Branch : bool Effect.t

type point = int -> bool

let xor : bool -> bool -> bool
(*@ xor(p, q): ex p, q; req true; ens res = p&&q @*)
  = fun p q -> (p && q)

let rec init : int -> (int -> bool) -> bool list 
(*@ init$(n, p, res): 
  req n=0; res=[]
  req n=1; p$(1, r); ens res=[r]
  req n>1; init$(n-1, p, r1); p$(n, r2); ens  res= r1@[r2] @*)
  = fun n p -> 
  match n with 
  | 0 -> []
  | 1 -> [p 1]
  | n -> (init (n-1) p) @ [p n]

let rec fold_left op acc list 
(*@ fold_left$(op, acc, list, res): 
  req list=[]; res=acc
  req list=h::t; op$(acc, h, acc'); fold_left$(op, acc', t, r); ens res=r @*)
= match list with 
  | []   -> acc
  | h :: t -> fold_left op (op acc h) t

let xor_predicate : int -> point -> bool
(*@ xor_predicate$(n, p, res): 
  req n=0; res=false
  req n=1; p$(1, r); ens res=r
  req n>1; xor_predicate$(n-1, p, r1); p$(n, r2); ens res= r1 && r2 @*)
  = fun n p ->
  match init n p with 
  | [] -> false
  | v :: vs -> fold_left xor v vs

let toss_twice () = 
  (*@ toss_twice(res): Branch(res1); Branch(res2); (res=res1@res2, Norm(res))  @*)
  (xor_predicate 2) (fun _ -> Effect.perform Branch) 

let _ =
  (*@ (counter -> 6 /\ solutions=1, Norm (())) @*)
  let counter = ref 0 in 
  let solutions = 
    match_with toss_twice ()
    { retc = (fun x -> if x then 1 else 0)
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | Branch ->
        Some (fun (k : (a, _) continuation) ->
           let open Multicont.Deep in
           let r = promote k in
           counter := !counter + 1;            (* increase the counter *)
           let tt = resume r true in
           counter := !counter + 1;            (* increase the counter *)
           let ff = resume r false in
           tt + ff)
      | _ -> None) } in
  Printf.printf "Res:%d\n" solutions;
  Printf.printf "Counter:%d\n" !counter

