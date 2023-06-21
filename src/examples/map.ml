
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let incr x = x + 1

let id y = y

let map_id ys
(*@ Norm(emp, ys) @*)
= map id ys

let x = ref 0 ;; 

let cl n = x := x + 1 ; n 

(* Norm (x -> a /\ l = length(li) /\ ret=list' /\ list'=li, li)  *)
let map_cl cl_in li = 
  let l = List.length li in 
  let list' = List.map (fun a -> cl_in a) li in 
  assert (!x = l); 
  list'
