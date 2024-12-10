
open Hipcore
open Hiptypes
open Pretty
open Debug

exception Norm_failure

let rec existStr str li =
  match li with
  | [] -> false
  | x :: xs -> if String.compare x str == 0 then true else existStr str xs

let rec list_of_heap h =
  match h with
  | EmptyHeap -> []
  | PointsTo (v, t) -> [(v, t)]
  | SepConj (h1, h2) -> list_of_heap h1 @ list_of_heap h2

let rec to_fixed_point f spec =
  let spec, changed = f spec in
  if not changed then spec else to_fixed_point f spec

let rec to_fixed_point_ptr_eq f spec =
  let spec1 = f spec in
  if spec == spec1 then spec else to_fixed_point_ptr_eq f spec

let rec simplify_term t : term  = 
  match t with 
  | Nil | TTrue | TFalse | UNIT | Num _ | TList _ | TTupple _ | Var _ | TApp _ | TLambda _  -> t
  | TNot a -> TNot (simplify_term a)
  | Rel (op, a, b) -> Rel (op, simplify_term a, simplify_term b)
  | Plus (Minus(t, Num n1), Num n2) -> 
    if n1 == n2 then t else if n1>= n2 then Minus(t, Num (n1-n2)) else Plus(t, Num (n1-n2))
  | Plus (a, b)  -> Plus (simplify_term a, simplify_term b)
  | TTimes (a, b)  -> TTimes (simplify_term a, simplify_term b)
  | TDiv (a, b)  -> TDiv (simplify_term a, simplify_term b)
  | Minus (a, b) -> Minus (simplify_term a, simplify_term b)
  | TAnd (a, b) -> TAnd (simplify_term a, simplify_term b)
  | TOr (a, b) -> TOr (simplify_term a, simplify_term b)
  | TPower(a, b) -> TPower (simplify_term a, simplify_term b)
  | TCons(a, b) -> TCons (simplify_term a, simplify_term b)

let simplify_pure (p : pi) : pi =
  let rec once p =
    match p with
    | Not (Atomic (EQ, a, TTrue)) -> (Atomic (EQ, a, TFalse), true)
    | (Atomic (EQ, TAnd(TTrue, TTrue), TTrue)) -> (True, true)
    | (Atomic (EQ, TAnd(TFalse, TTrue), TFalse)) -> (True, true)
    | (Atomic (EQ, t1, Plus(Num n1, Num n2))) -> (Atomic (EQ, t1, Num (n1+n2)), true)

    | Atomic (EQ, a, b) when a = b -> (True, true)
    | True | False | Atomic _ | Predicate _ | Subsumption _ -> (p, false)
    | And (True, a) | And (a, True) -> (a, true)
    | And (a, b) ->
      let a1, c1 = once a in
      let b1, c2 = once b in
      if c1 || c2 then (And (a1, b1), true) else (p, false)
    | Or (False, a) | Or (a, False) -> (a, true)
    | Or (a, b) ->
      let a1, c1 = once a in
      let b1, c2 = once b in
      if c1 || c2 then (Or (a1, b1), true) else (p, false)
    | Imply (a, b) ->
      let a1, c1 = once a in
      let b1, c2 = once b in
      if c1 || c2 then (Imply (a1, b1), true) else (p, false)
    | Not a ->
      let a1, c1 = once a in
      if c1 then (Not a1, true) else (p, false)
  in
  let r = to_fixed_point once p in
  (* (match (p, r) with
  | True, True -> ()
  | _ -> *)
    debug ~at:5 ~title:"simplify_pure" "%s\n==>\n%s" (string_of_pi p)
      (string_of_pi r)
      (* ) *)
      ;
  r

let rec simplify_heap h : kappa =
  let once h =
    match h with
    (*
  | SepConj (PointsTo (s1, t1), PointsTo (s2, t2)) -> 
    if String.compare s1 s2 == 0 then (PointsTo (s1, t1), Atomic(EQ, t1, t2))
    else (h, True)
  *)
    | SepConj (EmptyHeap, h1) -> (simplify_heap h1, true)
    | SepConj (h1, EmptyHeap) -> (simplify_heap h1, true)
    | PointsTo (str, t) -> (PointsTo (str, simplify_term t), false)
    | _ -> (h, false)
  in
  to_fixed_point once h

let simplify_state (p, h) = (simplify_pure p, simplify_heap h)
