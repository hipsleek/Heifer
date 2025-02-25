let toss ()
= shift k (let r1 = k true in let r2 = k false in r1 && r2)

(* Our tool cannot handle this example at the moment. We are treating
   disjunction in a wrong way.

   In a nutshell:
   phi_1; (phi_2 \/ phi_3) != (phi_1; phi_2) \/ (phi_1; phi_3)
   if phi_1 contains a shift.

   Currently, we infer this to be: (phi_1; phi_2) \/ (phi_1; phi_3)
   But it need to be: phi_1; (phi_2 \/ phi_3)
   And this error propagates to the downstream tasks...
 *)
let foo ()
(*@ ens res = false @*)
= reset (let v = toss () in if v then true else false)

let rec tossN n
= if n = 1 then
    toss ()
  else begin
    let r1 = toss () in
    let r2 = tossN (n - 1) in
    r1 && r2
  end
