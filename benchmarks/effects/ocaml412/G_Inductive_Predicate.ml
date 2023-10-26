open Printf

effect Inc : int -> int

let i = ref 0

let rec sumEff n
(* sumEff (n, res):
  req n=0; (res=0, Norm(res))
  req n>0; ex r; Inc$(n, r); ex tl; sumEff$(n-1, tl); (res=r+tl, Norm(res)) *)
= if n == 0 then 0
  else
    let r = perform (Inc n) in
    let tl = sumEff(n-1) in
    r + tl

let main i n
(*@ main(i, n, res): ex z; req (i->z/\n>=0); (i->z+(n*(n+1)/2) /\ res=n,Norm(res))  @*)
= match sumEff n with
  (*@ match_with (sumEff n, res): (i->z+(n*(n+1)/2) /\ res=n,Norm(res))  @*)
  | x -> x
  | exception e -> raise e
  | effect (Inc v) k -> i := !i+v; continue k 1
      (* i->!i+n;  match_with (sumEff (n-1), tl);   (Norm(1+tl)) *)
      (* i->!i+n; ex z; i-> z;  (i->z+(n-1*(n)/2) /\ tl=n-1,Norm(tl)) ;  (Norm(1+tl)) *)

let _ =
  let v = main i 10 in
  printf "%d\n" v
