open Core
open Core.Syntax
open Core.Pretty

type 'a tree =
  | Empty
  | Leaf of 'a
  | Node of 'a tree * 'a tree

let is_empty = function
  | Empty -> true
  | _ -> false

let node t1 t2 =
  match (t1, t2) with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _, _ -> Node (t1, t2)

let to_list t =
  let rec visit t acc =
    match t with
    | Empty -> acc
    | Leaf x -> x :: acc
    | Node (t1, t2) -> visit t1 (visit t2 acc)
  in
  visit t []

(* heap: always use sepconj *)
(* pure: can be under both conj/sepconj *)
let deep_destruct_mixed t =
  let rec visit = function
    | Emp -> (Empty, Empty)
    | True -> (Empty, Empty)
    | SepConj (t1, t2) ->
        let pure1, heap1 = visit t1 in
        let pure2, heap2 = visit t2 in
        (node pure1 pure2, node heap1 heap2)
    | Conj (t1, t2) ->
        let pure1, heap1 = visit t1 in
        let pure2, heap2 = visit t2 in
        if not (is_empty heap1 || is_empty heap2) then
          invalid_arg "deep_destruct_mixed: hprop / hprop is not allowed";
        (node pure1 pure2, node heap1 heap2)
    | t when Simply_typed.is_prop t -> (Leaf t, Empty)
    | t when Simply_typed.is_hprop t -> (Empty, Leaf t)
    | t -> invalid_arg (Format.asprintf "deep_destruct_mixed: %a" pp_term t)
  in
  let pure1, heap1 = visit t in
  (to_list pure1, to_list heap1)

let normalize_mixed t =
  let pure, heap = deep_destruct_mixed t in
  (Constr.conj pure, Constr.sepconj heap)
