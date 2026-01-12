open Bindlib
open Syntax

let open_dfun = function
  | Dfun (sym, def) -> sym, def

let open_psubsumes = function
  | Subsumes (s1, s2) -> s1, s2
  | _ -> invalid_arg "open_psubsumes: not PSubsumes"

let rec has_vars xs t : bool =
  match t with
  | Var x -> TVSet.mem x xs
  | Symbol _ -> false
  | Unit -> false
  | True -> false
  | False -> false
  | Int _ -> false
  | Nil -> false
  | Fun b -> mbinder_has_vars xs b
  | Tuple ts -> term_list_has_vars xs ts
  | Binop (_, t1, t2) -> has_vars xs t1 || has_vars xs t2
  | Unop (_, t) -> has_vars xs t
  | Conj (p1, p2) -> has_vars xs p1 || has_vars xs p2
  | Implies (p1, p2) -> has_vars xs p1 || has_vars xs p2
  | Subsumes (s1, s2) -> has_vars xs s1 || has_vars xs s2
  | Emp -> false
  | PointsTo (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | SepConj (p1, p2) -> has_vars xs p1 || has_vars xs p2
  | Requires p -> has_vars xs p
  | Ensures p -> has_vars xs p
  | Sequence (s1, s2) -> has_vars xs s1 || has_vars xs s2
  | Bind (s, b) -> has_vars xs s || binder_has_vars xs b
  | Apply (t1, t2) -> has_vars xs t1 || List.exists (has_vars xs) t2
  | Disj (s1, s2) -> has_vars xs s1 || has_vars xs s2
  | Forall b -> mbinder_has_vars xs b
  | Exists b -> mbinder_has_vars xs b
  | Shift b -> binder_has_vars xs b
  | Reset s -> has_vars xs s

and term_list_has_vars xs = List.exists (has_vars xs)

and binder_has_vars xs b =
  let _, p = unbind b in
  has_vars xs p

and mbinder_has_vars xs b =
  let _, s = unmbind b in
  has_vars xs s
