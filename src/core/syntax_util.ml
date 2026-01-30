open Bindlib
open Syntax
open Util

let open_dfun = function
  | Dfun (sym, def) -> (sym, def)

let open_disj_opt = function
  | Disj (t1, t2) -> Some (t1, t2)
  | _ -> None

let open_conj_opt = function
  | Conj (t1, t2) -> Some (t1, t2)
  | _ -> None

let open_subsumes_opt = function
  | Subsumes (t1, t2) -> Some (t1, t2)
  | _ -> None

let open_subsumes t =
  match open_subsumes_opt t with
  | Some (t1, t2) -> (t1, t2)
  | None -> invalid_arg (Format.asprintf "open_subsumes: %a" Pretty.pp_term t)

let open_requires_opt = function
  | Requires t -> Some t
  | _ -> None

let open_ensures_opt = function
  | Ensures t -> Some t
  | _ -> None

let open_implies_opt = function
  | Implies (t1, t2) -> Some (t1, t2)
  | _ -> None

let is_reset = function
  | Reset _ -> true
  | _ -> false

let is_emp = function
  | Emp -> true
  | _ -> false

let is_true = function
  | True -> true
  | _ -> false

let is_false = function
  | False -> true
  | _ -> false

let unseq = function
  | Sequence (t1, t2) -> t1, Some t2
  | t -> t, None

let unseq_open_ensures_opt t =
  let t1, t2 = unseq t in
  let open Options.Monad in
  let+ t1 = open_ensures_opt t1 in
  t1, t2

let unseq_open_requires_opt t =
  let t1, t2 = unseq t in
  let open Options.Monad in
  let+ t1 = open_requires_opt t1 in
  t1, t2

let unseq_tail_to_term = function
  | Some t -> t
  | None -> Unit

let reseq t = function
  | Some t' -> Sequence (t, t')
  | None -> t

let reseq_close_ensures t = reseq (Ensures t)

let reseq_close_requires t = reseq (Requires t)

let generalize x t = unbox (bind_var x (box_term t))

let mgeneralize xs t = unbox (bind_mvar xs (box_term t))

let mgeneralize_list xs ts = unbox (bind_mvar xs (box_term_list ts))

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
  | Conj (t1, t2)
  | Disj (t1, t2)
  | Implies (t1, t2)
  | Wand (t1, t2)
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

and list_has_vars xs = function
  | [] -> false
  | t :: ts -> has_vars xs t || list_has_vars xs ts

and binder_has_vars xs b =
  let _, t = unbind b in
  has_vars xs t

and mbinder_has_vars xs b =
  let _, t = unmbind b in
  has_vars xs t

let rec pre_get_vars acc = function
  | Var x -> TVSet.add x acc
  | Symbol _ -> acc
  | Unit -> acc
  | True -> acc
  | False -> acc
  | Int _ -> acc
  | Nil -> acc
  | Fun b -> pre_get_vars_mbinder acc b
  | Tuple ts -> pre_get_vars_list acc ts
  | Binop (_, t1, t2) -> pre_get_vars (pre_get_vars acc t1) t2
  | Unop (_, t) -> pre_get_vars acc t
  | Conj (t1, t2)
  | Disj (t1, t2)
  | Implies (t1, t2)
  | Wand (t1, t2)
  | Subsumes (t1, t2) -> pre_get_vars (pre_get_vars acc t1) t2
  | Emp -> acc
  | PointsTo (t1, t2) -> pre_get_vars (pre_get_vars acc t1) t2
  | SepConj (t1, t2) -> pre_get_vars (pre_get_vars acc t1) t2
  | Requires t -> pre_get_vars acc t
  | Ensures t -> pre_get_vars acc t
  | Sequence (t1, t2) -> pre_get_vars (pre_get_vars acc t1) t2
  | Bind (t, b) -> pre_get_vars_binder (pre_get_vars acc t) b
  | Apply (t, ts) -> pre_get_vars_list (pre_get_vars acc t) ts
  | Forall b -> pre_get_vars_mbinder acc b
  | Exists b -> pre_get_vars_mbinder acc b
  | Shift b -> pre_get_vars_binder acc b
  | Reset t -> pre_get_vars acc t

and pre_get_vars_list acc = function
  | [] -> acc
  | t :: ts -> pre_get_vars_list (pre_get_vars acc t) ts

and pre_get_vars_binder acc b =
  let x, t = unbind b in
  TVSet.remove x (pre_get_vars acc t)

and pre_get_vars_mbinder acc b =
  let xs, t = unmbind b in
  TVSet.diff (pre_get_vars acc t) (TVSets.of_array xs)

let get_vars t = pre_get_vars TVSet.empty t
