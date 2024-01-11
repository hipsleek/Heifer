
(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/all.rs *)

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

let has_property p xs = all p xs

let all_pos n
(*@ ex r ys; has_property(is_pos, ys, r); ens r=true/\res=ys @*)
= repeat 1 n

let test1 xs
(*@ req xs=[1;2;3;4]; ens res=false @*)
= let is_equal_four v = v = 4 in
  all is_equal_four xs

let test2 xs
(*@ req xs=[1;2;3;4]; ens res=true @*)
= let is_less_than_five v = v < 5 in
  all is_less_than_five xs

let test3 xs
(*@ req xs=[1;2;3;4]; ens res=false @*)
= let is_less_than_three v = v < 3 in
  all is_less_than_three xs
