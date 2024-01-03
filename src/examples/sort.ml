
let rec is_sorted xs =
  match xs with
  | [] -> true
  | x :: xs' -> (
    match xs' with
    | [] -> true
    | x' :: xs'' -> x <= x' && is_sorted xs'
  )

let rec insert_in_sorted_list v xs
= match xs with
  | [] -> [v]
  | x :: xs' -> if v <= x then v :: xs else x :: insert_in_sorted_list v xs'

let insert_in_sorted_list_ v xs (* FIXME *)
(*@
  ex t1 t2 r;
  is_sorted(xs, t1); req t1=true;
  insert_in_sorted_list(v, xs, r);
  is_sorted(r, t2); ens t2=true/\res=r
@*)
= insert_in_sorted_list v xs

let rec insertion_sort xs =
  match xs with
  | [] -> []
  | x :: xs' -> insert_in_sorted_list x (insertion_sort xs')

