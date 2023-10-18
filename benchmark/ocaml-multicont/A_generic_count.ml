(* Generic counting example based on Hillerström et al. (2020) https://arxiv.org/abs/2007.00605 *)

open Effect.Deep

type _ Effect.t += Branch : bool Effect.t

type point = int -> bool

let xor : bool -> bool -> bool
(*@ xor(p, q): ex p, q; req true; ens res = p&&q @*)
  = fun p q -> (p && q)


let init : int -> (int -> bool) -> bool list 
(*@ init$(n, p, res): 
  req n=0; p$(0, r); ens res=[r]
  req n>0; init$(n-1, p, r1); p$(n, r2); ens  res= r1@r2
@*)
  = fun n p -> 
  match n with 
  | 0 -> [p 0]
  | n -> (init (n-1) p) @ [p n]

let xor_predicate : int -> point -> bool
  = fun n p ->
  match init n p with 
  | [] -> false
  | v :: vs -> List.fold_left xor v vs

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

