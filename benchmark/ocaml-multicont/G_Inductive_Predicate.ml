open Printf
open Effect.Deep

type _ Effect.t += Inc : int -> int Effect.t

let i = ref 0

let rec sumEff n 
(* sumEff (n, res): 
  req n=0; (res=0, Norm(res))
  req n>0; ex r; Inc$(n, r); ex tl; sumEff$(n-1, tl); (res=r+tl, Norm(res)) *)
= if n == 0 then 0
  else 
    let r = Effect.perform (Inc n) in 
    let tl = sumEff(n-1) in 
    r + tl

let main i n 
(*@ main(i, n, res): ex z; req (i->z/\n>0); (i->z+(n*(n+1)/2) /\ res=n,Norm(res))  @*)
= match_with sumEff n 
  (*@ match_with (sumEff n, res): (i->z+(n*(n+1)/2) /\ res=n,Norm(res))  @*)
  { retc = (fun x -> x) 
  ; exnc = (fun e -> raise e)
  ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | Inc v -> Some (fun (k : (a, _) continuation) -> i := !i+v; continue k 1)
      (* i->!i+n;  match_with (sumEff (n-1), tl);   (Norm(1+tl)) *)
      (* i->!i+n; ex z; i-> z;  (i->z+(n-1*(n)/2) /\ tl=n-1,Norm(tl)) ;  (Norm(1+tl)) *)
      | _ -> None) }

let _ =
  let v = main i 10 in 
  printf "%d\n" v
