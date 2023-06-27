
let rec integers n =
  if n = 0 then []
  else n :: integers (n - 1)

let rec same x n =
  if n = 0 then []
  else x :: same x (n - 1)

let rec all p xs =
  match xs with
  | [] -> true
  | x :: xs1 -> p x && all p xs1

let is_pos x = x > 0

let is_one x = if x = 1 then true else false

let all_one n
(*@ ex xs; all(is_one, xs, true); Norm(emp, xs) @*)
= same 1 n

(* this can't be proved yet *)
(* it's also very slow, so it's not running for now *)

(* let all_pos n
(*@ ex xs; all(is_pos, xs, true); Norm(emp, xs) @*)
= same 1 n *)
