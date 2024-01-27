
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let id y = y

let map_id ys
(*@ ens res=ys @*)
= map id ys

let succ x = x + 1

let rec succ_list xs =
  match xs with
  | [] -> []
  | x :: xs1 -> succ x :: succ_list xs1

let map_succ ys
(*@ ex r; succ_list(ys, r); ens res=r @*)
= map succ ys

let rec thrice_list xs =
  match xs with
  | [] -> []
  | x :: xs' -> (x + x + x) :: thrice_list xs'

let map_thrice xs
(*@ ex ys; thrice_list(xs, ys); ens res=ys @*)
= let cl i = i + i + i in
  map cl xs
