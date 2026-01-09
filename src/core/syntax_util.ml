open Bindlib
open Syntax

let open_dfun d =
  match d with
  | Dfun (sym, def) -> sym, def

let rec term_has_vars xs t : bool =
  match t with
  | TVar x -> TVSet.mem x xs
  | TSymbol _ -> false
  | TUnit -> false
  | TTrue -> false
  | TFalse -> false
  | TInt _ -> false
  | TNil -> false
  | TFun b -> staged_spec_mbinder_has_vars xs b
  | TApp (_, ts) -> term_list_has_vars xs ts
  | TTuple ts -> term_list_has_vars xs ts
  | TBinop (_, t1, t2) -> term_has_vars xs t1 || term_has_vars xs t2
  | TUnop (_, t) -> term_has_vars xs t

and term_list_has_vars xs = List.exists (term_has_vars xs)

and prop_has_vars xs p =
  match p with
  | PAtom t -> term_has_vars xs t
  | PConj (p1, p2) -> prop_has_vars xs p1 || prop_has_vars xs p2
  | PImplies (p1, p2) -> prop_has_vars xs p1 || prop_has_vars xs p2
  | PSubsumes (s1, s2) -> staged_spec_has_vars xs s1 || staged_spec_has_vars xs s2
  | PForall b -> prop_binder_has_vars xs b

and prop_binder_has_vars xs b =
  let _, p = unmbind b in
  prop_has_vars xs p

and hprop_has_vars xs p =
  match p with
  | HPure p -> prop_has_vars xs p
  | HEmp -> false
  | HPointsTo (t1, t2) -> term_has_vars xs t1 || term_has_vars xs t2
  | HSepConj (p1, p2) -> hprop_has_vars xs p1 || hprop_has_vars xs p2

and staged_spec_has_vars xs s =
  match s with
  | Return t -> term_has_vars xs t
  | Requires p -> hprop_has_vars xs p
  | Ensures p -> hprop_has_vars xs p
  | Sequence (s1, s2) -> staged_spec_has_vars xs s1 || staged_spec_has_vars xs s2
  | Bind (s, b) -> staged_spec_has_vars xs s || staged_spec_binder_has_vars xs b
  | Apply (t1, t2) -> term_has_vars xs t1 || List.exists (term_has_vars xs) t2
  | Disjunct (s1, s2) -> staged_spec_has_vars xs s1 || staged_spec_has_vars xs s2
  | Forall b -> staged_spec_mbinder_has_vars xs b
  | Exists b -> staged_spec_mbinder_has_vars xs b
  | Shift b -> staged_spec_binder_has_vars xs b
  | Reset s -> staged_spec_has_vars xs s
  | Dollar _ -> failwith "todo"

and staged_spec_binder_has_vars xs b =
  let _, s = unbind b in
  staged_spec_has_vars xs s

and staged_spec_mbinder_has_vars xs b =
  let _, s = unmbind b in
  staged_spec_has_vars xs s
