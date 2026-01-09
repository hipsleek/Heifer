(** Implementation of first-order unification algorithm. *)

open Bindlib
open Core.Syntax

exception Unification_failure

(** Precondition: only [t1] contains unification variables. *)
let rec unify_term_aux t1 t2 uvars sigma =
  match t1, t2 with
  | TVar x, _ when TVSet.mem x uvars ->
      begin
        match TVMap.find_opt x sigma with
        | Some t -> unify_term_aux t t2 uvars sigma
        | None -> TVMap.add x t2 sigma
      end
  | TVar x1, TVar x2 when eq_vars x1 x2 -> sigma
  | TSymbol sym1, TSymbol sym2 when sym1 = sym2 -> sigma
  | TUnit, TUnit -> sigma
  | TTrue, TTrue -> sigma
  | TFalse, TFalse -> sigma
  | TInt i1, TInt i2 when i1 = i2 -> sigma
  | TFun b1, TFun b2 -> unify_staged_spec_mbinder_aux b1 b2 uvars sigma
  | TTuple ts1, TTuple ts2 -> unify_term_list_aux ts1 ts2 uvars sigma
  | TBinop (op1, t11, t12), TBinop (op2, t21, t22) when op1 = op2 ->
      let sigma = unify_term_aux t11 t21 uvars sigma in
      let sigma = unify_term_aux t12 t22 uvars sigma in
      sigma
  | TUnop (op1, t1), TUnop (op2, t2) when op1 = op2 -> unify_term_aux t1 t2 uvars sigma
  | TNil, TNil -> sigma
  | _, _ -> raise Unification_failure

and unify_term_list_aux ts1 ts2 uvars sigma =
  match ts1, ts2 with
  | [], [] -> sigma
  | t1 :: ts1, t2 :: ts2 ->
      let sigma = unify_term_aux t1 t2 uvars sigma in
      let sigma = unify_term_list_aux ts1 ts2 uvars sigma in
      sigma
  | _, _ -> raise Unification_failure

and unify_prop_aux p1 p2 uvars sigma =
  match p1, p2 with
  | PAtom t1, PAtom t2 -> unify_term_aux t1 t2 uvars sigma
  | PConj (p11, p12), PConj (p21, p22) ->
      let sigma = unify_prop_aux p11 p21 uvars sigma in
      let sigma = unify_prop_aux p12 p22 uvars sigma in
      sigma
  | _, _ -> raise Unification_failure

and unify_hprop_aux p1 p2 uvars sigma =
  match p1, p2 with
  | HPure p1, HPure p2 -> unify_prop_aux p1 p2 uvars sigma
  | HEmp, HEmp -> sigma
  | HPointsTo (t11, t12), HPointsTo (t21, t22) ->
      let sigma = unify_term_aux t11 t21 uvars sigma in
      let sigma = unify_term_aux t12 t22 uvars sigma in
      sigma
  | HSepConj (p11, p12), HSepConj (p21, p22) ->
      let sigma = unify_hprop_aux p11 p21 uvars sigma in
      let sigma = unify_hprop_aux p12 p22 uvars sigma in
      sigma
  | _, _ -> raise Unification_failure

and unify_staged_spec_aux s1 s2 uvars sigma =
  match s1, s2 with
  | Return t1, Return t2 -> unify_term_aux t1 t2 uvars sigma
  | Requires p1, Requires p2 -> unify_hprop_aux p1 p2 uvars sigma
  | Ensures p1, Ensures p2 -> unify_hprop_aux p1 p2 uvars sigma
  | Sequence (s11, s12), Sequence (s21, s22) ->
      let sigma = unify_staged_spec_aux s11 s21 uvars sigma in
      let sigma = unify_staged_spec_aux s12 s22 uvars sigma in
      sigma
  | Bind (s1, b1), Bind (s2, b2) ->
      let sigma = unify_staged_spec_aux s1 s2 uvars sigma in
      let sigma = unify_staged_spec_binder_aux b1 b2 uvars sigma in
      sigma
  | Apply (t11, t12), Apply (t21, t22) ->
      let sigma = unify_term_aux t11 t21 uvars sigma in
      let sigma =
        List.fold_right2 (fun c1 c2 sigma ->
            unify_term_aux c1 c2 uvars sigma) t12 t22 sigma
      in
      sigma
  | Disjunct (s11, s12), Disjunct (s21, s22) ->
      let sigma = unify_staged_spec_aux s11 s21 uvars sigma in
      let sigma = unify_staged_spec_aux s12 s22 uvars sigma in
      sigma
  | Forall _, Forall _ -> failwith "todo"
  | Exists b1, Exists b2 -> unify_staged_spec_mbinder_aux b1 b2 uvars sigma
  | Shift b1, Shift b2 -> unify_staged_spec_binder_aux b1 b2 uvars sigma
  | Reset s1, Reset s2 -> unify_staged_spec_aux s1 s2 uvars sigma
  | Dollar _, Dollar _ -> failwith "todo"
  (* | Dollar (s1, k1), Dollar (s2, k2) ->
      let sigma = unify_staged_spec_aux sigma s1 s2 in
      let sigma = unify_staged_spec_binder_aux sigma k1 k2 in
      sigma *)
  | _, _ -> raise Unification_failure

and unify_staged_spec_binder_aux b1 b2 uvars sigma =
  let _, s1, s2 = unbind2 b1 b2 in
  unify_staged_spec_aux s1 s2 uvars sigma

and unify_staged_spec_mbinder_aux b1 b2 uvars sigma =
  let _, s1, s2 = unmbind2 b1 b2 in
  unify_staged_spec_aux s1 s2 uvars sigma

(** The main entry point of the unification algorithm.

    Precondition: only [t1] contains unification variables. *)
let unify s1 s2 uvars = unify_staged_spec_aux s1 s2 uvars TVMap.empty
