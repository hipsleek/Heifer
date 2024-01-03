
let[@pure] rec length (li:int list) : int = 
  match li with 
  | [] -> 0
  | x :: xs -> 1 + length xs

(*
  lemma aa r =
    ens xs=[] <: ens length(xs)=0
@*)

let aa xs
(*@ ens length(xs)>=0 @*)
= xs