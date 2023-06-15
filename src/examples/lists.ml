
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let incr x = x + 1

let id y = y

let map_id ys
(*@ Norm(emp, ys) @*)
= map id ys
