
effect Inc : int -> int

let rec sumEff n
(*@ req n>=0 ; Norm(n=0 /\ res=0) 
  \/ex r; req n>=0; Inc(n>0, n, r); ex tl; sumEff(n-1, tl); Norm(res = r + tl) @*)
= if n == 0 then 0
  else
    let r = perform (Inc n) in
    let tl = sumEff(n-1) in
    r + tl

let main i n
(*@ ex z; req i->z/\n>=0; Norm(i->z+(n*(n+1)/2) ,n)  @*)
= match sumEff n with
(*@ ex z; req i->z; Norm(i -> z+(n*(n+1)/2), n) @*)
  | x -> x
  | exception e -> raise e
  | effect (Inc v) k -> i := !i+v; continue k 1

let test () 
  (*@ ex i; Norm(i->55, 10) @*) 
= let i = ref 0 in 
  let v = main i 10 in
  v