
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let id y = y

let map_id ys
(*@ Norm(emp, ys) @*)
= map id ys

let succ x = x + 1

let map_not_id_false ys
(*@ Norm(emp, ys) @*)
= map succ ys

(* ghost function that specifies what mapping succ should return *)
let rec succ_list xs =
  match xs with
  | [] -> []
  | x :: xs1 -> succ x :: succ_list xs1

(* we use succ_list in the statement of this lemma *)
let map_succ ys
(*@ ex r; succ_list(ys, r); Norm(emp, r) @*)
= map succ ys

(*
let x = ref 0 ;; 

let cl n = x := x + 1 ; n 

(* Norm (x -> a /\ l = length(li) /\ ret=list' /\ list'=li, li)  *)
let map_cl cl_in li = 
  let l = List.length li in 
  let list' = List.map (fun a -> cl_in a) li in 
  assert (!x = l); 
  list'
*)