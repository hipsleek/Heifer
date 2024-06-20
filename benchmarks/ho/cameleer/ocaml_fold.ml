(*@ open Seq *)

(*@ function seq_of_list (l: 'a list): 'a seq = match l with
      | [] -> empty
      | x :: r -> cons x (seq_of_list r) *)
(*@ coercion *)

(*@ lemma seq_of_list_append: forall l1 l2: 'a list.
      seq_of_list (List.append l1 l2) == seq_of_list l1 ++ seq_of_list l2 *)

(*@ predicate permitted (v: 'a seq) (s: 'a seq) =
      length v <= length s &&
      forall i. 0 <= i < length v -> v[i] = s[i] *)

(*@ predicate complete (l: 'a seq) (v: 'a seq) =
      length v = length l *)

let rec fold_left (v : 'a list) ((inv : 'b -> 'a seq -> bool) [@ghost])
    ((l0 : 'a list) [@ghost]) f (acc : 'b) = function
  | [] -> (acc, v)
  | x :: l -> fold_left (v @ [ x ]) inv l0 f (f acc x) l
(*@ r, vres = fold_left v inv l0 f acc param
      requires permitted v l0
      requires l0 == v ++ param
      requires inv acc v
      requires forall v acc x.
                 inv acc v -> permitted (snoc v x) l0 -> not (complete v l0) ->
                 inv (f acc x) (snoc v x)
      variant  param
      ensures  permitted vres l0 && vres == v ++ param && inv r vres *)

(*@ function sum_of_list (l: int list): int =
      match l with
      | [] -> 0
      | x :: r -> x + sum_of_list r *)

let rec summ (xs : int list) : int =
match xs with
  | [] -> 0
  | x :: l -> x + summ l
  (*@ res = summ xs
      ensures res = sum_of_list xs
      diverges *)

(*@ lemma sum_cons: forall x:int, xs: int list.
      SeqSum.sum (cons x xs) = x + SeqSum.sum xs *)

(*@ lemma seq_list_sum: forall xs: int list.
      SeqSum.sum (seq_of_list xs) = sum_of_list xs *)

let foldl_sum (xs:int list) : int =
      fst (fold_left [] (fun e p -> e = SeqSum.sum p) xs (fun t c -> c + t) 0 xs)
(*@ r = test xs
      ensures r = sum_of_list xs *)


(*@ lemma seq_list_length: forall xs: int list.
      length (seq_of_list xs) = List.length xs *)

let foldl_length (xs:int list) : int =
      fst (fold_left [] (fun e p -> e = length p) xs (fun t _ -> 1 + t) 0 xs)
(*@ r = test xs
      ensures r = List.length xs *)

let rec foldr ((inv : 'b -> 'a seq -> bool) [@ghost])
      (f : 'a -> 'b -> 'b) (xs : 'a list) (acc : 'b)
= match xs with
  | [] -> acc
  | x :: t -> f x (foldr inv f t acc)
(*@ r = foldr inv f xs acc
      requires inv acc []
      requires forall acc x ys.
                 inv acc ys -> inv (f x acc) (cons x ys)
      variant  xs
      ensures  inv r xs *)

let foldr_length (xs:int list) : int =
      foldr (fun e p -> e = length p) (fun _ t -> 1 + t) xs 0
(*@ r = test xs
     ensures r = List.length xs *)

let foldr_sum (xs:int list) : int =
      foldr (fun e p -> e = SeqSum.sum p) (fun c t -> c + t) xs 0
(*@ r = test xs
      ensures r = sum_of_list xs *)