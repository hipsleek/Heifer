effect Flip : bool

let rec tossNtimeTail n 
(* tossNtimeTail(n, res) = ens n=1; Flip(res)  \/ 
                    ex r1; ens n>1; Flip(r1); ex r2; tossNtimeTail(n-1, r2); ens res=r1 && r2 *)
= match n with 
| 1 -> perform Flip
| n -> let r1 = perform Flip in 
       let r2 = tossNtimeTail (n-1) in r1 && r2

(* \phi_inv(n,acc,r) = ex w ; req counter -> w ens[r] counter -> w+(2^(n+1) -2) /\ (acc/\r=1 \/ !acc/\r=0) *)
(* lemma: ex res; tossNtimeTail(n,res); ens[acc'] acc'=(acc /\ res) catch H ⊑ ex r; \phi_inv(n,acc,r) *)

let tossHandlerTail counter n : int  (*  counter = !counter + 2^(n+1) - 2 *)
= match tossNtimeTail n with 
  | x -> if x then 1 else 0                
  | effect Flip k ->
      counter := !counter + 1;            (* increase the counter *)
      let res1 = continue (Obj.clone_continuation k) true in         (* resume with true     *)
      counter := !counter + 1;            (* increase the counter *)
      let res2 = continue k false in      (* resume with false    *)
      res1 + res2                         (* gather the results   *)
(*proof (deep):
       counter := !counter + 1; counter := !counter + (2^(n) -2;  counter := !counter + 1; counter := !counter + (2^(n) -2;  
       counter := !counter + 1 + (2^(n) -2) + 1 + (2^(n) -2) = !counter + 2^(n+1) -2
*)

(* 
lemma: ex res; tossNtimeTail(n,res); \Phi catch H ⊑ counter := !counter + 1; tossNtimeTail(n-1,res); counter := !counter + 1; tossNtimeTail(n-1,res);
proof (shallow): 
      counter := !counter + 1; tossNtimeTail(n-1,res);  counter := !counter + 1; tossNtimeTail(n-1,res);  
*)


let rec tossNtimeNonTail n 
(* tossNtimeTail(n, res) = ens n=1; Flip(res)  \/ 
                    ex r1; ens n>1; tossNtimeTail(n-1, r1); ex r2; Flip(r2); ens res=r1 && r2 *)

(* tossNtimeTail(n, res) = ens n=1; Flip(res)  \/ 
                    ex r1; ens n>1; tossNtimeTail(n-1, r1); ens counter := !counter + 2 /\ (r1\/ false) *)

= match n with 
| 1 -> perform Flip
| n -> let r1 = tossNtimeNonTail (n-1) in 
       let r2 = perform Flip in r1 && r2


(* \phi_inv'(n,acc,s,r) = ex w ; req counter -> w ens[r] counter -> w + ((2^n -1) * s) /\ (acc/\r=1 \/ !acc/\r=0) *)
(* lemma: ex res; tossNtimeNonTail(n,res); counter -> counter + s catch H ⊑ ex r; \phi_inv'(n,acc,s,r) *)


(* \phi_inv'(n,acc,r) = ex w ; req counter -> w ens[r] counter -> w + 2^(n+2)-2 /\ (acc/\r=1 \/ !acc/\r=0) *)
(* lemma: ex res; tossNtimeNonTail(n,res); counter -> counter + 2 catch H ⊑ ex r; \phi_inv'(n,acc,r) *)


let tossHandlerNonTail counter n : int   (*  counter = !counter + 2^(n+1) - 2 *)
= match tossNtimeNonTail n with 
  | x -> if x then 1 else 0                
  | effect Flip k ->
      counter := !counter + 1;            (* increase the counter *)
      let res1 = continue (Obj.clone_continuation k) true in         (* resume with true     *)
      counter := !counter + 1;            (* increase the counter *)
      let res2 = continue k false in       (* resume with false    *)
      res1 + res2                         (* gather the results   *)

(*
proof: counter := !counter + ??? ; counter := !counter + 1;   counter := !counter + 1;
       counter :=  (2^n - 1) * (2)           
       = !counter + 2^(n+1) -2
*)


(* lemma: ex res; try tossNtimeTailShallow(1,res); \phi catch H ⊑ counter -> counter + 1;  \phi; counter + 1;  \phi; *)
(* lemma: ex res; try n > 1 /\ tossNtimeTailShallow(n,res); \phi catch H ⊑ 
   counter -> counter + 1; tossNtimeTailShallow(n-1,res); \phi; counter + 1;  tossNtimeTailShallow(n-1,res);  \phi; *)

let _ = 
   let counter = ref 0 in 
   let res = tossHandlerTail counter 9 in 
   print_endline (string_of_int !counter);
   print_endline (string_of_int res);
   let counter1 = ref 0 in 
   let res = tossHandlerNonTail counter1 9 in 
   print_endline (string_of_int !counter1);
   print_endline (string_of_int res)