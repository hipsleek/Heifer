open Bindlib
open Syntax

let open_dfun = function
  | Dfun (sym, def) -> sym, def

let open_subsumes = function
  | Subsumes (t1, t2) -> t1, t2
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

let unseq_open_ensures_opt = function
  | Ensures t -> Some (t, Unit)
  | Sequence (Ensures t1, t2) -> Some (t1, t2)
  | _ -> None

let unseq_open_requires_opt = function
  | Requires t -> Some (t, Unit)
  | Sequence (Requires t1, t2) -> Some (t1, t2)
  | _ -> None

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
  | Conj (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | Disj (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | Implies (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | Subsumes (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | Emp -> false
  | PointsTo (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | SepConj (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | Requires t -> has_vars xs t
  | Ensures t -> has_vars xs t
  | Sequence (t1, t2) -> has_vars xs t1 || has_vars xs t2
  | Bind (t, b) -> has_vars xs t || binder_has_vars xs b
  | Apply (t, ts) -> has_vars xs t || list_has_vars xs ts
  | Forall b -> mbinder_has_vars xs b
  | Exists b -> mbinder_has_vars xs b
  | Shift b -> binder_has_vars xs b
  | Reset t -> has_vars xs t

and list_has_vars xs =
  List.exists (has_vars xs)

and binder_has_vars xs b =
  let _, t = unbind b in
  has_vars xs t

and mbinder_has_vars xs b =
  let _, t = unmbind b in
  has_vars xs t
