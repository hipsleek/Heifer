
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let incr x = x + 1


let sum () : int list
(*@ Norm(emp, 1) @*)
= map incr [1; 2]
