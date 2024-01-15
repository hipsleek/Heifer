
let[@pure] rec is_sorted (xs: int list): bool =
  match xs with
  | [] -> true
  | x :: xs' -> (
    match xs' with
    | [] -> true
    | x' :: xs'' -> x <= x' && is_sorted xs'
  )

let[@pure] rec insert_in_sorted_list (v: int) (xs: int list): int list
= match xs with
  | [] -> [v]
  | x :: xs' -> if v <= x then v :: xs else x :: insert_in_sorted_list v xs'

let[@pure] insert_in_sorted_list_ (v: int) (xs: int list): int list (* FIXME *)
(*@ req is_sorted(xs)=true; ex r; ens is_sorted(r)=true/\res=r @*)
= insert_in_sorted_list v xs

let rec insertion_sort xs =
  match xs with
  | [] -> []
  | x :: xs' -> insert_in_sorted_list x (insertion_sort xs')

