open Bindlib
open Core.Syntax

type cont =
  | CNil
  | CCons0 of term * cont
  | CCons1 of (term, term) binder * cont

let rec refine_cont (s : term) (k : cont) : term =
  match k with
  | CNil -> s
  | CCons0 (s', k) -> Sequence (s, refine_cont s' k)
  | CCons1 (b, k) ->
      let x, s' = unbind b in
      Bind (s, unbox (bind_var x (box_term (refine_cont s' k))))

let capture_cont (k : cont) : term =
  match k with
  | CNil ->
      let x = new_tvar "x" in
      unbox (Mk.fun_ (bind_mvar [|x|] ((Mk.var x))))
  | CCons0 (s, k) ->
      let x = new_tvar "_" in
      unbox (Mk.fun_ (bind_mvar [|x|] (box_term (Reset (refine_cont s k)))))
  | CCons1 (b, k) ->
      let x, s = unbind b in
      unbox (Mk.fun_ (bind_mvar [|x|] (box_term (Reset (refine_cont s k)))))


(** Simplify a term, using zeta reduction strategy.
    Zeta reduction: reduce all local bindings ([Sequence] and [Bind]). *)
let rec simpl_zeta t =
  fst (simpl_zeta_aux t)

and simpl_zeta_list ts =
  fst (simpl_zeta_list_aux ts)

and simpl_zeta_binder b =
  let x, t = unbind b in
  unbox (bind_var x (box_term (simpl_zeta t)))

and simpl_zeta_mbinder b =
  let xs, t = unmbind b in
  unbox (bind_mvar xs (box_term (simpl_zeta t)))

(** Do the actual simplification and return a [bool] indicating whether the
    resulting term is a pure term or not. If a term is pure, it is safe to be
    substituted to a binding. *)
and simpl_zeta_aux t =
  match t with
  | Var _
  | Symbol _
  | Unit
  | True
  | False
  | Int _
  | Nil -> t, true
  | Fun b -> Fun (simpl_zeta_mbinder b), true
  | Tuple ts ->
      let ts, p = simpl_zeta_list_aux ts in
      Tuple ts, p
  | Binop (op, t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      Binop (op, t1, t2), p1 && p2
  | Unop (op, t) ->
      let t, p = simpl_zeta_aux t in
      Unop (op, t), p
  | Conj (t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      Conj (t1, t2), p1 && p2
  | Disj (t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      Disj (t1, t2), p1 && p2
  | Implies (t1, t2) ->
      let t1, p1 = simpl_zeta_aux t1 in
      let t2, p2 = simpl_zeta_aux t2 in
      Implies (t1, t2), p1 && p2
  | Subsumes (t1, t2) -> Subsumes (simpl_zeta t1, simpl_zeta t2), false
  | Emp -> t, false
  | PointsTo (t1, t2) -> PointsTo (simpl_zeta t1, simpl_zeta t2), false
  | SepConj (t1, t2) -> SepConj (simpl_zeta t1, simpl_zeta t2), false
  | Requires t -> Requires (simpl_zeta t), false
  | Ensures t -> Ensures (simpl_zeta t), false
  | Sequence (t1, t2) ->
      let t1, p = simpl_zeta_aux t1 in
      if p then simpl_zeta_aux t2 else Sequence (t1, simpl_zeta t2), false
  | Bind (t, b) ->
      let t, p = simpl_zeta_aux t in
      if p then simpl_zeta_aux (subst b t) else Bind (t, simpl_zeta_binder b), false
  | Apply (t, ts) -> Apply (simpl_zeta t, simpl_zeta_list ts), false
  | Forall b -> Forall (simpl_zeta_mbinder b), false
  | Exists b -> Exists (simpl_zeta_mbinder b), false
  | Shift b -> Shift (simpl_zeta_binder b), false
  | Reset t -> Reset (simpl_zeta t), false

and simpl_zeta_list_aux ts =
  match ts with
  | [] -> [], true
  | t :: ts ->
      let t, p = simpl_zeta_aux t in
      let ts, ps = simpl_zeta_list_aux ts in
      t :: ts, p && ps


(** Simplify a term, using associativity of bind and sequence.

    This auxiliary function returns a [box] for efficiency. The [box] will be
    unboxed once at the end. *)
let rec simpl_assoc_box t =
  match t with
  | Conj (t1, t2) -> Mk.conj (simpl_assoc_box t1) (simpl_assoc_box t2)
  | Disj (t1, t2) -> Mk.disj (simpl_assoc_box t1) (simpl_assoc_box t2)
  | Forall b -> Mk.forall (simpl_assoc_box_mbinder b)
  | Exists b -> Mk.exists (simpl_assoc_box_mbinder b)
  | Shift b -> Mk.shift (simpl_assoc_box_binder b)
  | Reset t -> Mk.reset (simpl_assoc_box t)
  | Sequence (t1, t2) -> simpl_assoc_box_cont t1 (fun tb -> Mk.sequence tb (simpl_assoc_box t2))
  | Bind (t, b) -> simpl_assoc_box_cont t (fun tb -> Mk.bind tb (simpl_assoc_box_binder b))
  | _ -> box_term t

and simpl_assoc_box_binder b =
  let x, t = unbind b in
  bind_var x (simpl_assoc_box t)

and simpl_assoc_box_mbinder b =
  let xs, t = unmbind b in
  bind_mvar xs (simpl_assoc_box t)

and simpl_assoc_box_cont t k =
  match t with
  | Conj (t1, t2) -> k (Mk.conj (simpl_assoc_box t1) (simpl_assoc_box t2))
  | Disj (t1, t2) -> k (Mk.disj (simpl_assoc_box t1) (simpl_assoc_box t2))
  | Forall b -> k (Mk.forall (simpl_assoc_box_mbinder b))
  | Exists b -> k (Mk.exists (simpl_assoc_box_mbinder b))
  | Shift b -> k (Mk.shift (simpl_assoc_box_binder b))
  | Reset t -> k (Mk.reset (simpl_assoc_box t))
  | Sequence (t1, t2) -> simpl_assoc_box_cont t1 (fun tb -> Mk.sequence tb (simpl_assoc_box_cont t2 k))
  | Bind (t, b) -> simpl_assoc_box_cont t (fun tb -> Mk.bind tb (simpl_assoc_box_binder_cont b k))
  | _ -> k (box_term t)

and simpl_assoc_box_binder_cont b k =
  let x, t = unbind b in
  bind_var x (simpl_assoc_box_cont t k)

(** Simplify a term, using associativity of bind and sequence. *)
let simpl_assoc t = unbox (simpl_assoc_box t)


(** Simplify a term, using beta reduction strategy.
    Beta reduction: reduce all applications of [Fun]. *)
let simpl_beta t = ignore t; failwith "todo"


(** This is the main entry point for [shift/reset reduction].

    TODO: rewrite this. *)
let rec reduce_staged_spec (s : term) : term =
  match s with
  | Requires p -> Requires p
  | Ensures p -> Ensures p
  | Sequence (s1, s2) -> Sequence (reduce_staged_spec s1, reduce_staged_spec s2)
  | Bind (s, b) -> Bind (reduce_staged_spec s, b)
  | Apply (f, t) -> Apply (f, t)
  | Disj (s1, s2) -> Disj (reduce_staged_spec s1, reduce_staged_spec s2)
  | Forall b -> Forall b
  | Exists b -> Exists b
  | Shift b -> Shift b
  | Reset s -> reduce_staged_spec_cont s CNil
  | _ -> s

(** This function is called only when we visit the body of a [Reset] during
    shift/reset reduction. *)
and reduce_staged_spec_cont (s : term) (k : cont) : term =
  match s with
  | Requires p -> Sequence (Requires p, reduce_invoke_cont k Unit) (* Float requires outside of reset *)
  | Ensures p -> Sequence (Ensures p, reduce_invoke_cont k Unit)
  | Sequence (s1, s2) -> reduce_staged_spec_cont s1 (CCons0 (s2, k))
  | Bind (s, b) -> reduce_staged_spec_cont s (CCons1 (b, k))
  | Apply (f, t) -> Reset (refine_cont (Apply (f, t)) k)
  | Disj (s1, s2) -> Disj (reduce_staged_spec_cont s1 k, reduce_staged_spec_cont s2 k)
  | Forall b -> Reset (refine_cont (Forall b) k)
  | Exists b -> Reset (refine_cont (Exists b) k)
  | Shift b -> reduce_staged_spec_cont (subst b (capture_cont k)) CNil
  | Reset s -> reduce_staged_spec_cont (reduce_staged_spec_cont s CNil) k
  | _ -> reduce_invoke_cont k s

and reduce_invoke_cont (k : cont) (t : term) : term =
  match k with
  | CNil -> t
  | CCons0 (s, k) -> reduce_staged_spec_cont s k
  | CCons1 (b, k) -> reduce_staged_spec_cont (subst b t) k

let simpl_term t =
  simpl_assoc (simpl_zeta t)
