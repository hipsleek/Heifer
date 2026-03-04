
let[@pure] rec length (li:int list) : int = 
  match li with 
  | [] -> 0
  | x :: xs -> 1 + length xs

(*@
  lemma length_length xs res =
    length(xs, res) ==> ens res=length(xs)
@*)

let length_length xs
(*@ ens res=length(xs) @*)
= length xs
