
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let incr x = x + 1

(* cannot be proved without an induction hypothesis. we can't specify the elements of lists *)
let map_inc_false ()
(*@ Norm(emp, [2; 3]) @*)
= map incr [1; 2]

let test1_true ()
(*@ Norm(emp, [1; 2]) @*)
= [1; 2]

let test2_false ()
(*@ Norm(emp, [2; 2]) @*)
= [1; 2]

let test3_true ()
(*@ Norm(emp, [0; 1; 2]) @*)
= 0 :: [1; 2]

let test4_true xs
(*@ Norm(emp, [0]) \/ Norm(emp, xs) @*)
= match xs with
  | [] -> [0]
  | x :: xs1 -> x :: xs1