
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let id y = y

let map_id ys
= map id ys
(*@ ens res=ys @*)

let succ x = x + 1

let map_not_id_false ys
= map succ ys
(*@ ens res=ys @*)

(* ghost function that specifies what mapping succ should return *)
let rec succ_list xs =
  match xs with
  | [] -> []
  | x :: xs1 -> succ x :: succ_list xs1

(* we use succ_list in the statement of this lemma *)
let map_succ ys
= map succ ys
(*@ ex r; succ_list(ys, r); ens res=r @*)

let rec thrice_list xs =
  match xs with
  | [] -> []
  | x :: xs' -> (x + x + x) :: thrice_list xs'

let map_thrice xs
= let cl i = i + i + i in
  map cl xs
(*@ ex ys; thrice_list(xs, ys); ens res=ys @*)
