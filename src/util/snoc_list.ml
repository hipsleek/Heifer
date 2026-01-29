type 'a snoc_list =
  | Lin
  | Snoc of 'a snoc_list * 'a

let snoc xs x = Snoc (xs, x)

let rec fold_right f xs acc =
  match xs with
  | Lin -> acc
  | Snoc (xs, x) -> fold_right f xs (f x acc)

let append_list xs =
  List.fold_left snoc xs

let to_list xs =
  fold_right (fun x acc -> x :: acc) xs []

let of_list xs =
  List.fold_left snoc Lin xs
