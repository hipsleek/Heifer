(** Implementation of first-order unification algorithm. *)

open Bindlib
open Core.Syntax

exception Unification_failure

(** Precondition: only [t1] contains unification variables. *)
let rec unify_term_aux t1 t2 uvars sigma =
  match t1, t2 with
  | Var x, _ when TVSet.mem x uvars ->
      begin
        match TVMap.find_opt x sigma with
        | Some t -> unify_term_aux t t2 uvars sigma
        | None -> TVMap.add x t2 sigma
      end
  | Var x1, Var x2 when eq_vars x1 x2 -> sigma
  | Symbol sym1, Symbol sym2 when sym1 = sym2 -> sigma
  | Unit, Unit -> sigma
  | True, True -> sigma
  | False, False -> sigma
  | Int i1, Int i2 when i1 = i2 -> sigma
  | Fun b1, Fun b2 -> unify_mbinder_aux b1 b2 uvars sigma
  | Tuple ts1, Tuple ts2 -> unify_term_list_aux ts1 ts2 uvars sigma
  | Binop (op1, t11, t12), Binop (op2, t21, t22) when op1 = op2 ->
      let sigma = unify_term_aux t11 t21 uvars sigma in
      let sigma = unify_term_aux t12 t22 uvars sigma in
      sigma
  | Unop (op1, t1), Unop (op2, t2) when op1 = op2 -> unify_term_aux t1 t2 uvars sigma
  | Nil, Nil -> sigma
  | Conj (p11, p12), Conj (p21, p22) ->
      let sigma = unify_term_aux p11 p21 uvars sigma in
      let sigma = unify_term_aux p12 p22 uvars sigma in
      sigma
  | Emp, Emp -> sigma
  | PointsTo (t11, t12), PointsTo (t21, t22) ->
      let sigma = unify_term_aux t11 t21 uvars sigma in
      let sigma = unify_term_aux t12 t22 uvars sigma in
      sigma
  | SepConj (p11, p12), SepConj (p21, p22) ->
      let sigma = unify_term_aux p11 p21 uvars sigma in
      let sigma = unify_term_aux p12 p22 uvars sigma in
      sigma
  | Requires p1, Requires p2 -> unify_term_aux p1 p2 uvars sigma
  | Ensures p1, Ensures p2 -> unify_term_aux p1 p2 uvars sigma
  | Sequence (s11, s12), Sequence (s21, s22) ->
      let sigma = unify_term_aux s11 s21 uvars sigma in
      let sigma = unify_term_aux s12 s22 uvars sigma in
      sigma
  | Bind (s1, b1), Bind (s2, b2) ->
      let sigma = unify_term_aux s1 s2 uvars sigma in
      let sigma = unify_binder_aux b1 b2 uvars sigma in
      sigma
  | Apply (t11, t12), Apply (t21, t22) ->
      let sigma = unify_term_aux t11 t21 uvars sigma in
      let sigma =
        List.fold_right2 (fun c1 c2 sigma ->
            unify_term_aux c1 c2 uvars sigma) t12 t22 sigma
      in
      sigma
  | Disj (s11, s12), Disj (s21, s22) ->
      let sigma = unify_term_aux s11 s21 uvars sigma in
      let sigma = unify_term_aux s12 s22 uvars sigma in
      sigma
  | Forall _, Forall _ -> failwith "todo"
  | Exists b1, Exists b2 -> unify_mbinder_aux b1 b2 uvars sigma
  | Shift b1, Shift b2 -> unify_binder_aux b1 b2 uvars sigma
  | Reset s1, Reset s2 -> unify_term_aux s1 s2 uvars sigma
  | _, _ -> raise Unification_failure

and unify_term_list_aux ts1 ts2 uvars sigma =
  match ts1, ts2 with
  | [], [] -> sigma
  | t1 :: ts1, t2 :: ts2 ->
      let sigma = unify_term_aux t1 t2 uvars sigma in
      let sigma = unify_term_list_aux ts1 ts2 uvars sigma in
      sigma
  | _, _ -> raise Unification_failure

(* and unify_prop_aux p1 p2 uvars sigma = *)
  (* match p1, p2 with *)
  (* | Atom t1, Atom t2 -> unify_term_aux t1 t2 uvars sigma *)
  (* | _, _ -> raise Unification_failure *)

(* and unify_hprop_aux p1 p2 uvars sigma =
  match p1, p2 with
  (* | HPure p1, HPure p2 -> unify_prop_aux p1 p2 uvars sigma *)
  | _, _ -> raise Unification_failure *)

(* and unify_term_aux s1 s2 uvars sigma = *)
  (* match s1, s2 with *)
  (* | Return t1, Return t2 -> unify_term_aux t1 t2 uvars sigma *)

  (* | _, _ -> raise Unification_failure *)

and unify_binder_aux b1 b2 uvars sigma =
  let _, s1, s2 = unbind2 b1 b2 in
  unify_term_aux s1 s2 uvars sigma

and unify_mbinder_aux b1 b2 uvars sigma =
  let _, s1, s2 = unmbind2 b1 b2 in
  unify_term_aux s1 s2 uvars sigma

(** The main entry point of the unification algorithm.

    Precondition: only [t1] contains unification variables. *)
let unify s1 s2 uvars = unify_term_aux s1 s2 uvars TVMap.empty
