let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs' -> f x :: map f xs'

let map_shift_reset_aux xs =
  shift (fun k -> map k xs)

let map_shift_reset f xs =
  reset (f (map_shift_reset_aux xs))

let id x = x

let succ x = x + 1

(*
  lemma map_shift_reset_id xs res =
    map_shift_reset(id, xs, res) ==> ens res=xs
 *)
(* Fatal error: exception Failure("maps not disjoint on key v34") *)

let map_id xs
(* ens res=xs *)
(* Fatal error: exception Failure("maps not disjoint on key v34") *)
= map_shift_reset id xs

let empty_list ()
(*@ ens res = [] @*)
= map id []

let singleton_list ()
(*@ ens res = [1] @*)
= map id [1]
(* cannot be proven atm *)

let empty_list_v1 ()
(*@ ens res = [] @*)
= map succ []

let singleton_list_v1 ()
(*@ ens res = [1] @*)
= map succ [0]
(* cannot be proven atm *)
