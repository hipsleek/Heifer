open Printf
open Effect.Deep

type _ Effect.t += Inc : int -> int Effect.t

let i = ref 0

let rec sumEff n 
= if n == 0 then 0
  else let r = Effect.perform (Inc n) in r + sumEff(n-1)

let main i n 
= match_with sumEff n 
  { retc = (fun x -> x)
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | Inc v -> Some (fun (k : (a, _) continuation) -> i := !i+v; continue k 1)
      | _ -> None) }

let _ =
  let v = main i 10 in 
  printf "%d\n" v
