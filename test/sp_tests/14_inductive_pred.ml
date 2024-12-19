effect Inc : int -> int 


(*@
sumEff(n,res) = n=0 /\ res=n
  \/ n>0 /\ ex r; (emp, Inc(n,r)); 
     ex r2; (emp, sumEff(n-1,r2)); 
     (emp, Norm(r+r2))
@*)

let rec sumEff n 
(* req n>=0; (emp, sumEff(n,res)) *)
= if n == 1 then 1
  else 
    let r = perform (Inc n) in 
    r + sumEff(n-1)

let handler n 
(* req n>=0; ex i; (i->n(n-1)/2, Norm(n)) *)
= let i = ref 0 in 
  match sumEff n with
  | v -> print_endline ("i = " ^ string_of_int !i); v
  | effect (Inc v) k -> i := !i + v -1; continue k 1

let main = 
  let r = handler 5 in 
  print_endline ("r = " ^ string_of_int r)