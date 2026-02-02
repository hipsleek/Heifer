open Bindlib
open Core.Syntax
open Core.Syntax_util

let return_unit = function
  | Requires _ | Ensures _ -> true
  | _ -> false

(** Simplify a term, using zeta reduction strategy. Zeta reduction: reduce all
    local bindings ([Sequence] and [Bind]). *)
let rec simpl_zeta t = fst (simpl_zeta_aux t)

and simpl_zeta_list ts = fst (simpl_zeta_list_aux ts)

and simpl_zeta_binder b =
  let x, t = unbind b in
  generalize x (simpl_zeta t)

and simpl_zeta_mbinder b =
  let xs, t = unmbind b in
  mgeneralize xs (simpl_zeta t)

(** Do the actual simplification and return a [bool] indicating whether the
    resulting term is a pure term or not. If a term is pure, it is safe to be
    substituted to a binding. *)
and simpl_zeta_aux t =
  match t with
  | Var _ | Symbol _ | Unit | True | False | Int _ | Nil -> (t, true)
  | Fun b -> (Fun (simpl_zeta_mbinder b), true)
  | Tuple ts ->
      let ts, p = simpl_zeta_list_aux ts in
      (Tuple ts, p)
  | Binop (op, t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      (Binop (op, t1, t2), p1 && p2)
  | Unop (op, t) ->
      let t, p = simpl_zeta_aux t in
      (Unop (op, t), p)
  | Conj (t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      (Conj (t1, t2), p1 && p2)
  | Disj (t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      (Disj (t1, t2), p1 && p2)
  | Implies (t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      (Implies (t1, t2), p1 && p2)
  | Subsumes (t1, t2) -> (Subsumes (simpl_zeta t1, simpl_zeta t2), false)
  | Emp -> (t, false)
  | PointsTo (t1, t2) -> (PointsTo (simpl_zeta t1, simpl_zeta t2), false)
  | SepConj (t1, t2) -> (SepConj (simpl_zeta t1, simpl_zeta t2), false)
  | Wand (t1, t2) -> (Wand (simpl_zeta t1, simpl_zeta t2), false)
  | Requires t -> (Requires (simpl_zeta t), false)
  | Ensures t -> (Ensures (simpl_zeta t), false)
  | Sequence (t1, t2) ->
      let t1, p = simpl_zeta_aux t1 in
      if p then simpl_zeta_aux t2 else (Sequence (t1, simpl_zeta t2), false)
  | Bind (t, b) ->
      let t, p = simpl_zeta_aux t in
      if p then simpl_zeta_aux (subst b t)
      else if return_unit t then (Sequence (t, simpl_zeta (subst b Unit)), false)
      else (Bind (t, simpl_zeta_binder b), false)
  | Apply (t, ts) -> (Apply (simpl_zeta t, simpl_zeta_list ts), false)
  | Forall b -> (Forall (simpl_zeta_mbinder b), false)
  | Exists b -> (Exists (simpl_zeta_mbinder b), false)
  | Shift b -> (Shift (simpl_zeta_binder b), false)
  | Reset t -> (Reset (simpl_zeta t), false)

and simpl_zeta_list_aux ts =
  match ts with
  | [] -> ([], true)
  | t :: ts ->
      let t, p = simpl_zeta_aux t in
      let ts, ps = simpl_zeta_list_aux ts in
      (t :: ts, p && ps)

(** Simplify a term, using associativity of bind and sequence.

    This auxiliary function returns a [box] for efficiency. The [box] will be
    unboxed once at the end. *)
let rec box_simpl_assoc t =
  match t with
  | Conj (t1, t2) -> Mk.conj (box_simpl_assoc t1) (box_simpl_assoc t2)
  | Disj (t1, t2) -> Mk.disj (box_simpl_assoc t1) (box_simpl_assoc t2)
  | Forall b -> Mk.forall (box_simpl_assoc_mbinder b)
  | Exists b -> Mk.exists (box_simpl_assoc_mbinder b)
  | Shift b -> Mk.shift (box_simpl_assoc_binder b)
  | Reset t -> Mk.reset (box_simpl_assoc t)
  | Sequence (t1, t2) -> box_simpl_assoc_cont t1 (fun tb -> Mk.sequence tb (box_simpl_assoc t2))
  | Bind (t, b) -> box_simpl_assoc_cont t (fun tb -> Mk.bind tb (box_simpl_assoc_binder b))
  | Subsumes (t1, t2) -> Mk.subsumes (box_simpl_assoc t1) (box_simpl_assoc t2)
  | _ -> box_term t

and box_simpl_assoc_binder b =
  let x, t = unbind b in
  bind_var x (box_simpl_assoc t)

and box_simpl_assoc_mbinder b =
  let xs, t = unmbind b in
  bind_mvar xs (box_simpl_assoc t)

and box_simpl_assoc_cont t k =
  match t with
  | Conj (t1, t2) -> k (Mk.conj (box_simpl_assoc t1) (box_simpl_assoc t2))
  | Disj (t1, t2) -> Mk.disj (box_simpl_assoc_cont t1 k) (box_simpl_assoc_cont t2 k)
  | Forall b -> k (Mk.forall (box_simpl_assoc_mbinder b))
  | Exists b -> k (Mk.exists (box_simpl_assoc_mbinder b))
  | Shift b -> k (Mk.shift (box_simpl_assoc_binder b))
  | Reset t -> k (Mk.reset (box_simpl_assoc t))
  | Sequence (t1, t2) -> box_simpl_assoc_cont t1 (fun tb -> Mk.sequence tb (box_simpl_assoc_cont t2 k))
  | Bind (t, b) -> box_simpl_assoc_cont t (fun tb -> Mk.bind tb (box_simpl_assoc_binder_cont b k))
  | _ -> k (box_term t)

and box_simpl_assoc_binder_cont b k =
  let x, t = unbind b in
  bind_var x (box_simpl_assoc_cont t k)


(** Simplify a term, using associativity of bind and sequence. *)
let simpl_assoc t = unbox (box_simpl_assoc t)

(** Simplify a term, using beta reduction strategy. Beta reduction: reduce all
    applications of [Fun].

    Note: be careful when calling this function! It will loop if a term which
    has no beta-normal form is passed as argument.

    TODO: this is the naive implementation. It can be more efficient. *)
let rec simpl_beta t =
  match t with
  | Var _ | Symbol _ | Unit | True | False | Int _ | Nil | Emp -> t
  | Fun b -> Fun (simpl_beta_mbinder b)
  | Tuple ts -> Tuple (simpl_beta_list ts)
  | Binop (op, t1, t2) -> Binop (op, simpl_beta t1, simpl_beta t2)
  | Unop (op, t) -> Unop (op, simpl_beta t)
  | Conj (t1, t2) -> Conj (simpl_beta t1, simpl_beta t2)
  | Disj (t1, t2) -> Disj (simpl_beta t1, simpl_beta t2)
  | Implies (t1, t2) -> Implies (simpl_beta t1, simpl_beta t2)
  | Wand (t1, t2) -> Wand (simpl_beta t1, simpl_beta t2)
  | Subsumes (t1, t2) -> Subsumes (simpl_beta t1, simpl_beta t2)
  | PointsTo (t1, t2) -> PointsTo (simpl_beta t1, simpl_beta t2)
  | SepConj (t1, t2) -> SepConj (simpl_beta t1, simpl_beta t2)
  | Requires t -> Requires (simpl_beta t)
  | Ensures t -> Ensures (simpl_beta t)
  | Sequence (t1, t2) -> Sequence (simpl_beta t1, simpl_beta t2)
  | Bind (t, b) -> Bind (simpl_beta t, simpl_beta_binder b)
  | Apply (t, ts) -> simpl_beta_step (simpl_beta t) (simpl_beta_list ts)
  | Forall b -> Forall (simpl_beta_mbinder b)
  | Exists b -> Exists (simpl_beta_mbinder b)
  | Shift b -> Shift (simpl_beta_binder b)
  | Reset t -> Reset (simpl_beta t)

and simpl_beta_list ts = List.map simpl_beta ts

and simpl_beta_binder b =
  let x, t = unbind b in
  generalize x (simpl_beta t)

and simpl_beta_mbinder b =
  let xs, t = unmbind b in
  mgeneralize xs (simpl_beta t)

and simpl_beta_step t ts =
  match t with
  | Fun b -> simpl_beta (msubst b (Array.of_list ts))
  | _ -> Apply (t, ts)

let simpl t = simpl_zeta (Prenex.prenex_assoc (simpl_beta t))
