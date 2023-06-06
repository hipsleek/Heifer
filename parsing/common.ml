let rec split_last xs =
  match xs with
  | [] -> failwith "split_last"
  | [x] -> ([], x)
  | x :: xs ->
    let init, last = split_last xs in
    (x :: init, last)

let rec replace_nth n y xs =
  match (n, xs) with
  | 0, [] -> []
  | 0, _ :: xs -> y :: xs
  | _, [] -> []
  | _, x :: xs1 -> x :: replace_nth (n - 1) y xs1
