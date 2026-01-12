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

(* BROKEN: need type-checking to work properly *)
let rec simpl_term (t : term) : term =
  match t with
  (* Computational / Spec terms *)
  | Sequence (s1, s2) -> simpl_staged_spec_cont s1 (CCons0 (s2, CNil))
  | Bind (s, b) -> simpl_staged_spec_cont s (CCons1 (b, CNil))
  | Apply (f, ts) ->
      begin
        match f with
        | Fun b -> simpl_term (msubst b (Array.of_list ts))
        | _ -> Apply (simpl_term f, List.map simpl_term ts)
      end
  | Disj (s1, s2) -> Disj (simpl_term s1, simpl_term s2)
  | Requires p -> Requires (simpl_term p)
  | Ensures p -> Ensures (simpl_term p)
  | Shift b -> Shift b (* TODO: simplify inside binder? *)
  | Reset s -> Reset (simpl_term s)
  | Forall b -> Forall b
  | Exists b -> Exists b

  (* Pure / Structural terms *)
  | Var _ -> t
  | Symbol _ -> t
  | Unit -> Unit
  | Nil -> Nil
  | True -> True
  | False -> False
  | Int _ -> t
  | Emp -> Emp
  | Tuple ts -> Tuple (List.map simpl_term ts)
  | Binop (op, t1, t2) -> Binop (op, simpl_term t1, simpl_term t2)
  | Unop (op, t) -> Unop (op, simpl_term t)
  | PointsTo (t1, t2) -> PointsTo (simpl_term t1, simpl_term t2)
  | SepConj (h1, h2) -> SepConj (simpl_term h1, simpl_term h2)
  | Conj (p1, p2) -> Conj (simpl_term p1, simpl_term p2)
  | Implies (p1, p2) -> Implies (simpl_term p1, simpl_term p2)
  | Subsumes (s1, s2) -> Subsumes (simpl_term s1, simpl_term s2)
  | Fun b -> Fun b

and simpl_staged_spec_cont (s : term) (k : cont) : term =
  match s with
  | Requires p -> Sequence (Requires (simpl_term p), simpl_invoke_cont k Unit)
  | Ensures p -> Sequence (Ensures (simpl_term p), simpl_invoke_cont k Unit)
  | Sequence (s1, s2) -> simpl_staged_spec_cont s1 (CCons0 (s2, k))
  | Bind (s, b) -> simpl_staged_spec_cont s (CCons1 (b, k))
  | Apply (f, ts) ->
      begin
        match f with
        | Fun b -> simpl_staged_spec_cont (msubst b (Array.of_list ts)) k
        | _ -> refine_cont (Apply (simpl_term f, List.map simpl_term ts)) k
      end
  | Disj (s1, s2) -> Disj (simpl_staged_spec_cont s1 k, simpl_staged_spec_cont s2 k)
  | Forall _ -> refine_cont s k
  | Exists _ -> refine_cont s k
  | Shift _ -> refine_cont s k
  | Reset s -> refine_cont (Reset (simpl_term s)) k
  (* Treat everything else as a return value *)
  | _ -> simpl_invoke_cont k (simpl_term s)

and simpl_invoke_cont (k : cont) (t : term) =
  match k with
  | CNil -> t
  | CCons0 (s, k) -> simpl_staged_spec_cont s k
  | CCons1 (b, k) -> simpl_staged_spec_cont (subst b t) k

(* TODO: do we simplify under binder? *)

(** This is the main entry point for [shift/reset reduction]. *)
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
