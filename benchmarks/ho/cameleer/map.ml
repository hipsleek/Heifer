
(*@ open Seq *)

(*@ function seq_of_list (l: 'a list): 'a seq = match l with
      | [] -> empty
      | x :: r -> cons x (seq_of_list r) *)
(*@ coercion *)

(*@ lemma seq_of_list_append: forall l1 l2: 'a list.
      seq_of_list (List.append l1 l2) == seq_of_list l1 ++ seq_of_list l2 *)

let rec map (f:'a -> 'b) (xs:'a list) =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1
(*@ ys = map f xs
      variant xs
      ensures length ys = length xs
      ensures forall i. 0 <= i < length ys -> ys[i] = f (xs[i]) *)

let id y = y
(*@ res = id x
    ensures x = res *)

(*@ lemma length_seq_of_list: forall l1 l2: 'a list.
      length (seq_of_list l2) = 0 -> l2 = Nil *)

(*@ lemma index_shift: forall x:'a, xs:'a list, i:int.
    1 <= i /\ i < length (Cons x xs) -> (Cons x xs)[i] = xs[i-1] *)

(*@ lemma length_smaller: forall xs ys: 'a list, x: 'a.
    length xs = length ys ->
    (forall i: int. 0 <= i /\ i <= length xs -> (Cons x xs)[i] = (Cons x ys)[i]) ->
    (forall i: int. 0 <= i /\ i < length xs -> (seq_of_list xs)[i] = (seq_of_list ys)[i]) *)

(*@ lemma equal_length_and_elements: forall l1 l2: 'a list.
      length l1 = length l2 ->
      (forall i. 0 <= i < length l1 -> l1[i] = l2[i]) ->
      l1 = l2 *)

let map_id ys = map id ys
(*@ r = map_id ys
    ensures r = ys *)

(*@ lemma index_shift_gen: forall p: ('a -> 'a). forall x:'a, xs:'a list, i:int.
    1 <= i /\ i < length (Cons x xs) -> p (Cons x xs)[i] = p xs[i-1] *)

(*@ lemma index_shift_p1: forall x:int, xs:int list, i:int.
    1 <= i /\ i < length (Cons x xs) -> 1 + (Cons x xs)[i] = 1 + xs[i-1] *)

(*@ lemma length_smaller_p1: forall xs ys: int list, x: int.
    length xs = length ys ->
    (forall i: int. 0 <= i /\ i <= length xs -> 1 + (Cons x xs)[i] = 1 + (Cons x ys)[i]) ->
    (forall i: int. 0 <= i /\ i < length xs -> 1 + (seq_of_list xs)[i] = 1 + (seq_of_list ys)[i]) *)

let map_succ ys = map (fun x -> x + 1) ys
(*@ r = map_succ ys
    ensures forall i:int. 0<=i /\ i<length ys -> r[i] = ys[i] + 1 *)

(*@ function succ_list (xs:int list): int list =
  match xs with
  | [] -> []
  | x::xs1 -> (x+1) :: succ_list xs1 *)

let map_succ1 ys =
  map (fun x -> x + 1) ys
(*@ r = map_succ1 ys
    ensures r = succ_list ys *)


let map_thrice ys = map (fun x -> x * 3) ys
(*@ r = map_thrice ys
    ensures forall i:int. 0<=i /\ i<length ys -> r[i] = ys[i] * 3 *)
