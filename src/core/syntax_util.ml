open Bindlib
open Syntax

let open_dfun = function
  | Dfun (sym, def) -> sym, def

let open_subsumes = function
  | Subsumes (s1, s2) -> s1, s2
  | _ -> invalid_arg "open_subsumes: not PSubsumes"

let is_emp = function
  | Emp -> true
  | _ -> false

let is_true = function
  | True -> true
  | _ -> false

let is_false = function
  | False -> true
  | _ -> false

let rec has_vars xs = function
  | Var x -> TVSet.mem x xs
  | Symbol _ -> false
  | Unit -> false
  | True -> false
  | False -> false
  | Int _ -> false
  | Nil -> false
  | Fun b -> mbinder_has_vars xs b
  | Tuple ts -> list_has_vars xs ts
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
  | Apply (t, ts) -> has_vars xs t || list_has_vars xs ts
  | Disj (s1, s2) -> has_vars xs s1 || has_vars xs s2
  | Forall b -> mbinder_has_vars xs b
  | Exists b -> mbinder_has_vars xs b
  | Shift b -> binder_has_vars xs b
  | Reset s -> has_vars xs s

and list_has_vars xs = function
  | [] -> false
  | t :: ts -> has_vars xs t || list_has_vars xs ts

and binder_has_vars xs b =
  let _, p = unbind b in
  has_vars xs p

and mbinder_has_vars xs b =
  let _, s = unmbind b in
  has_vars xs s
