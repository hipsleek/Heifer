
let[@pure] rec is_sorted (xs: int list): bool =
  match xs with
  | [] -> true
  | x :: xs' -> (
    match xs' with
    | [] -> true
    (* Note: && is not yet supported *)
    | x' :: xs'' -> if x <= x' then is_sorted xs' else false
  )

let rec insert_in_sorted_list v xs
= match xs with
  | [] -> [v]
  | x :: xs' -> if v <= x then v :: xs else x :: insert_in_sorted_list v xs'

let insert_in_sorted_list_spec v xs (* FIXME *)
(*@ req is_sorted(xs)=true; ens is_sorted(res)=true @*)
= insert_in_sorted_list v xs

let rec insertion_sort xs = (* FIXME *)
  match xs with
  | [] -> []
  | x :: xs' -> insert_in_sorted_list_spec x (insertion_sort xs')

let insertion_sort_spec xs (* FIXME *)
(*@ ens is_sorted(xs)=true @*)
= insertion_sort xs
