open Core.Pretty
open Core.Syntax
open Util

type heaplet = term * term
type heap = heaplet list

let prepend_equality t1 t2 equalities =
  if equal_term t1 t2 then equalities else Constr.eq t1 t2 :: equalities

(* This is O(n^2) at the moment. It can be more efficient. *)
let rec match_heap h1 h2 =
  match h1 with
  | [] -> [], [], h2, []
  | hl1 :: h1 ->
      let x1, t1 = hl1 in
      let handle_heaplet (x2, t2) = if equal_term x1 x2 then Some t2 else None in
      match Lists.find_remove_map handle_heaplet h2 with
      | None ->
          let common, h1, h2, equalities = match_heap h1 h2 in
          common, hl1 :: h1, h2, equalities
      | Some (t2, h2) ->
          let common, h1, h2, equalities = match_heap h1 h2 in
          let equalities = prepend_equality t1 t2 equalities in
          hl1 :: common, h1, h2, equalities

let hprop_to_heaplet = function
  | PointsTo (t1, t2) -> t1, t2
  | t -> invalid_arg (Format.asprintf "hprop_to_heaplet: %a" pp_term t)

let hprop_list_to_heap = List.map hprop_to_heaplet

let hprop_to_heap t =
  let rec visit t acc =
    match t with
    | Emp -> acc
    | PointsTo (t1, t2) -> (t1, t2) :: acc
    | SepConj (t1, t2) -> visit t1 (visit t2 acc)
    | _ -> invalid_arg (Format.asprintf "hprop_to_heap: %a" pp_term t)
  in
  visit t []

let heaplet_to_hprop (t1, t2) = PointsTo (t1, t2)

let heap_to_hprop_list = List.map heaplet_to_hprop

let heap_to_hprop h = Constr.sepconj (heap_to_hprop_list h)

let deep_destruct_sepconj t =
  let rec visit t acc =
    match t with
    | Emp -> acc
    | PointsTo _ -> t :: acc
    | SepConj (t1, t2) -> visit t1 (visit t2 acc)
    | _ -> invalid_arg (Format.asprintf "deep_destruct_sepconj: %a" pp_term t)
  in
  visit t []

let biab_list ts1 ts2 =
  let h1 = hprop_list_to_heap ts1 in
  let h2 = hprop_list_to_heap ts2 in
  let _, h1, h2, equalities = match_heap h1 h2 in
  heap_to_hprop_list h1, heap_to_hprop_list h2, equalities

let biab t1 t2 =
  let h1 = hprop_to_heap t1 in
  let h2 = hprop_to_heap t2 in
  let _, h1, h2, equalities = match_heap h1 h2 in
  heap_to_hprop h1, heap_to_hprop h2, Constr.conj equalities

let pairwise_inequalites xs ys =
  let open Lists.Monad in
  let* x = xs in
  let* y = ys in
  pure (Binop (Neq, x, y))

let xpure (h : hprop) : prop =
  let rec run h =
    match h with
    | Emp -> (True, [])
    | PointsTo (x, _) -> (Binop (Gt, x, Int 0), [x])
    | SepConj (a, b) ->
        let a, xs = run a in
        let b, ys = run b in
        (Conj (a, Conj (b, Constr.conj (pairwise_inequalites xs ys))), xs @ ys)
    | _ -> (h, [])
  in
  fst (run h)
