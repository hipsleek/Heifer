
let rec snoc lst x =
  match lst with
  | [] -> [x]
  | y :: ys -> y :: snoc ys x

let rec reverse lst =
  match lst with
  | [] -> []
  | x :: xs -> snoc (reverse xs) x 
  
let rec subsequence sub lst =
  match lst with
  | [] -> (match sub with
    | [] -> true
    | _ -> false)
  | x :: xs -> (match sub with
    | [] -> true
    | y :: ys -> if x == y then subsequence ys xs else subsequence sub xs)

let rec find lst y =
  match lst with
  | [] -> 0
  | x :: xs -> if x = y then 0 else 1 + (find xs y)

let rec replace lst x y =
  match lst with
  | [] -> []
  | h :: tail -> if h = x then y :: replace tail x y else h :: replace tail x y

let rec interleave xs ys =
  match xs with
  | [] -> ys
  | x :: xs' -> match ys with
  | [] -> xs
  | y :: ys' -> x :: (y :: interleave xs' ys')
