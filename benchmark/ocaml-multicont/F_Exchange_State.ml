open Printf
open Effect.Deep

type _ Effect.t += Exchange : int -> int Effect.t
let l = ref 5

let exchange (m:int)
= Effect.perform (Exchange m)
  
let exc_handler (l:int ref) (new_v:int)
=  match_with exchange new_v   
    { retc = (fun x -> x)
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | Exchange n -> Some (fun (k : (a, _) continuation) -> 
          let old_v = !l in l := n; 
          continue k old_v)
      | _ -> None) }

let _ = 
  let i = exc_handler l 10 in 
  printf "%d\n" i ;
  let i = exc_handler l 10 in 
  printf "%d\n" i 
