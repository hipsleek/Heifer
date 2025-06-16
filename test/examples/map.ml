
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let id y = y

let map_id ys
(*@ ens res=ys @*)
= map id ys

let [@pure] succ (x:int) : int = x + 1

let map_not_id_false ys
(*@ ens res=ys @*)
= map succ ys

let [@pure] rec succ_list (xs:int list) : int list =
  match xs with
  | [] -> []
  | x :: xs1 -> succ x :: succ_list xs1

(* we use succ_list in the statement of this lemma *)
let map_succ ys
(*@ ens res=succ_list(ys) @*)
= map succ ys

let [@pure] rec thrice_list (xs:int list) : int list =
  match xs with
  | [] -> []
  | x :: xs' -> (x + x + x) :: thrice_list xs'

let map_thrice xs
(*@ ens res=thrice_list(xs) @*)
= let cl i = i + i + i in
  map cl xs
