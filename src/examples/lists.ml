
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let incr x = x + 1


let map_inc_false ()
(*@ Norm(emp, [2; 3]) @*)
= map incr [1; 2]

let id y = y

let map_id xs
(*@ Norm(emp, xs) @*)
= map id xs
