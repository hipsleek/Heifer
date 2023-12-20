
let rec integers n =
  if n <= 0 then []
  else n :: integers (n - 1)

let rec repeat x n =
  if n <= 0 then []
  else x :: repeat x (n - 1)

let rec all p xs =
  match xs with
  | [] -> true
  | x :: xs1 -> p x && all p xs1

let is_pos x = x > 0

let has_property p xs =
  all p xs;
  xs

let all_pos n
(*@ ex r; has_property(is_pos, res, r); ens res=r @*)
= repeat 1 n
