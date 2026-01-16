module Monad = struct
  let pure x = [x]
  let ( let+ ) xs f = List.map f xs
  let ( let* ) xs f = List.concat_map f xs
end

let rec make n x =
  if n <= 0 then [] else x :: make (n - 1) x

let rec unsnoc_aux y = function
  | [] -> [], y
  | x :: xs ->
      let xs, x = unsnoc_aux x xs in
      y :: xs, x

let unsnoc = function
  | [] -> invalid_arg "unsnoc: empty list"
  | x :: xs -> unsnoc_aux x xs

let rec fold_right1_aux f y = function
  | [] -> y
  | x :: xs -> f y (fold_right1_aux f x xs)

let fold_right1 f = function
  | [] -> invalid_arg "fold_right1: empty list"
  | x :: xs -> fold_right1_aux f x xs

let fold_left1 f = function
  | [] -> invalid_arg "fold_left1: empty list"
  | x :: xs -> List.fold_left f x xs

let rec set_nth n y = function
  | [] -> []
  | x :: xs -> if n = 0 then y :: xs else x :: set_nth (n - 1) y xs

let rec init_aux y = function
  | [] -> []
  | x :: xs -> y :: init_aux x xs

let init = function
  | [] -> invalid_arg "init: empty list"
  | x :: xs -> init_aux x xs

let rec find_remove_opt f = function
  | [] -> None
  | x :: xs ->
      if f x then Some (x, xs)
      else
        match find_remove_opt f xs with
        | None -> None
        | Some (y, xs) -> Some (y, x :: xs)

let rec find_remove_map f = function
  | [] -> None
  | x :: xs ->
      match f x with
      | Some y -> Some (y, xs)
      | None ->
          match find_remove_map f xs with
          | None -> None
          | Some (y, xs) -> Some (y, x :: xs)

let product xs ys =
  List.concat_map (fun x -> List.map (fun y -> (x, y)) ys) xs
