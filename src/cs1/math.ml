
(* NUS CS1101S Reading Assessment 1 18/19 S1 *)

(* This is expected to fail since modulo operator is unimplemented *)
let is_even_false x (*@ req x>0 @*) = x mod 2 = 0
let rec even_or_odd_false x
(*@
  req x>0; ex r; is_even(x, r); ens r=true/\res=true
  \/ req x>0; ex r; is_even(x, r); ens r=false/\res=false
@*)
= if x = 1 then false
  else if x = 2 then true
  else even_or_odd_false (x - 2)

let min_of_three a b c
(*@
  ens a<b/\a<=c/\res=a
  \/ ens b<=a/\b<c/\res=b
  \/ ens c<=a/\c<=b/\res=c
@*)
= if a < b then if a < c then a else c
  else if b < c then b else c

let xor a b
(*@
  req a=true/\b=true; ens res=false
  \/ req a=true/\b=false; ens res=true
  \/ req a=false/\b=true; ens res=true
  \/ req a=false/\b=false; ens res=false
@*)
= not (a = b)
