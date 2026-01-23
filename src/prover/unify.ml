(** Implementation of first-order unification algorithm. *)

open Bindlib
open Core.Syntax
open Core.Syntax_util

exception Unification_failure

(** Precondition: only [t1] contains unification variables. *)
let rec unify_uvar x t uvars bvars sigma =
  match TVMap.find_opt x sigma with
  | None ->
      if has_vars bvars t then raise Unification_failure; (* bound variable escapes! *)
      TVMap.add x t sigma
  | Some t' -> unify_exact t' t uvars bvars sigma

and unify_exact t1 t2 uvars bvars sigma =
  match (t1, t2) with
  | Var x, _ when TVSet.mem x uvars -> unify_uvar x t2 uvars bvars sigma
  | Var x1, Var x2 when eq_vars x1 x2 -> sigma
  | Symbol sym1, Symbol sym2 when sym1 = sym2 -> sigma
  | Unit, Unit -> sigma
  | True, True -> sigma
  | False, False -> sigma
  | Int i1, Int i2 when i1 = i2 -> sigma
  | Fun b1, Fun b2 -> unify_mbinder_exact b1 b2 uvars bvars sigma
  | Tuple ts1, Tuple ts2 -> unify_list_exact ts1 ts2 uvars bvars sigma
  | Binop (op1, t11, t12), Binop (op2, t21, t22) when op1 = op2 ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | Unop (op1, t1), Unop (op2, t2) when op1 = op2 -> unify_exact t1 t2 uvars bvars sigma
  | Nil, Nil -> sigma
  | Conj (t11, t12), Conj (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | Disj (t11, t12), Disj (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | Implies (t11, t12), Implies (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | Subsumes (t11, t12), Subsumes (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | Emp, Emp -> sigma
  | PointsTo (t11, t12), PointsTo (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | SepConj (t11, t12), SepConj (t21, t22)
  | Wand (t11, t12), Wand (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | Requires t1, Requires t2 -> unify_exact t1 t2 uvars bvars sigma
  | Ensures t1, Ensures t2 -> unify_exact t1 t2 uvars bvars sigma
  | Sequence (t11, t12), Sequence (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      let sigma = unify_exact t12 t22 uvars bvars sigma in
      sigma
  | Bind (s1, b1), Bind (s2, b2) ->
      let sigma = unify_exact s1 s2 uvars bvars sigma in
      let sigma = unify_binder_exact b1 b2 uvars bvars sigma in
      sigma
  | Apply (t1, ts1), Apply (t2, ts2) ->
      let sigma = unify_exact t1 t2 uvars bvars sigma in
      let sigma = unify_list_exact ts1 ts2 uvars bvars sigma in
      sigma
  | Forall b1, Forall b2 -> unify_mbinder_exact b1 b2 uvars bvars sigma
  | Exists b1, Exists b2 -> unify_mbinder_exact b1 b2 uvars bvars sigma
  | Shift b1, Shift b2 -> unify_binder_exact b1 b2 uvars bvars sigma
  | Reset s1, Reset s2 -> unify_exact s1 s2 uvars bvars sigma
  | _, _ -> raise Unification_failure

and unify_list_exact ts1 ts2 uvars bvars sigma =
  match (ts1, ts2) with
  | [], [] -> sigma
  | t1 :: ts1, t2 :: ts2 ->
      let sigma = unify_exact t1 t2 uvars bvars sigma in
      let sigma = unify_list_exact ts1 ts2 uvars bvars sigma in
      sigma
  | _, _ -> raise Unification_failure

and unify_binder_exact b1 b2 uvars bvars sigma =
  let x, s1, s2 = unbind2 b1 b2 in
  unify_exact s1 s2 uvars (TVSet.add x bvars) sigma

and unify_mbinder_exact b1 b2 uvars bvars sigma =
  if mbinder_arity b1 <> mbinder_arity b2 then raise Unification_failure;
  let xs, s1, s2 = unmbind2 b1 b2 in
  unify_exact s1 s2 uvars (TVSet.add_seq (Array.to_seq xs) bvars) sigma

and unify_modulo_assoc t1 t2 uvars bvars sigma =
  match t1, t2 with
  | Sequence (t11, t12), Sequence (t21, t22) ->
      let sigma = unify_exact t11 t21 uvars bvars sigma in
      unify_modulo_assoc t12 t22 uvars bvars sigma
  | Bind (t1, b1), Bind (t2, b2) ->
      let sigma = unify_exact t1 t2 uvars bvars sigma in
      unify_binder_modulo_assoc b1 b2 uvars bvars sigma
  | _, Sequence (t21, t22) ->
      let sigma = unify_exact t1 t21 uvars bvars sigma in
      sigma, Some (fun t -> Sequence (t, t22))
  | _, Bind (t2, b2) ->
      let sigma = unify_exact t1 t2 uvars bvars sigma in
      sigma, Some (fun t -> Bind (t, b2))
  | _, _ ->
      let sigma = unify_exact t1 t2 uvars bvars sigma in
      sigma, None

and unify_binder_modulo_assoc b1 b2 uvars bvars sigma =
  let x, t1, t2 = unbind2 b1 b2 in
  unify_modulo_assoc t1 t2 uvars (TVSet.add x bvars) sigma

(* and unify_pattern _ =
  failwith "todo" *)

(** The main entry point of the unification algorithm.

    Precondition: only [t1] contains unification variables. *)
let unify t1 t2 uvars = unify_modulo_assoc t1 t2 uvars TVSet.empty TVMap.empty
