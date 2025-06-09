let rec unsnoc_aux y = function
  | [] -> [], y
  | x :: xs ->
      let xs', x' = unsnoc_aux x xs in
      y :: xs', x'

let unsnoc = function
  | [] -> failwith "unsnoc"
  | x :: xs -> unsnoc_aux x xs

let rec foldr1_aux f y = function
  | [] -> y
  | x :: xs -> f y (foldr1_aux f x xs)

let foldr1 f = function
  | [] -> failwith "foldr1"
  | x :: xs -> foldr1_aux f x xs

let foldl1 f = function
  | [] -> failwith "foldl1"
  | x :: xs -> List.fold_left f x xs

let rec replace_nth n y = function
  | [] -> []
  | x :: xs -> if n = 0 then y :: xs else x :: replace_nth (n - 1) y xs

let init xs =
  fst (unsnoc xs)