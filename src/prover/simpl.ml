open Bindlib
open Core.Syntax

type cont =
  | CNil
  | CCons0 of staged_spec * cont
  | CCons1 of (term, staged_spec) binder * cont

let rec refine_cont (s : staged_spec) (k : cont) : staged_spec =
  match k with
  | CNil -> s
  | CCons0 (s', k) -> Sequence (s, refine_cont s' k)
  | CCons1 (b, k) ->
      let x, s' = unbind b in
      Bind (s, unbox (bind_var x (box_staged_spec (refine_cont s' k)))) (* TODO: inefficient, we should work in box and only unbox at the end! *)

let capture_cont (k : cont) : term =
  match k with
  | CNil ->
      let x = new_tvar "x" in
      unbox (Mk.tfun (bind_var x (Mk.return (Mk.tvar x))))
  | CCons0 (s, k) ->
      let x = new_tvar "_" in
      unbox (Mk.tfun (bind_var x (box_staged_spec (Reset (refine_cont s k)))))
  | CCons1 (b, k) ->
      let x, s = unbind b in
      unbox (Mk.tfun (bind_var x (box_staged_spec (Reset (refine_cont s k)))))

let rec simpl_term (t : term) : term =
  match t with
  | TVar _ -> t
  | TUnit -> TUnit
  | TNil -> TNil
  | TTrue -> TTrue
  | TFalse -> TFalse
  | TInt _ -> t
  | TTuple ts -> TTuple (List.map simpl_term ts)
  | TFun b -> TFun b
      (* let b = simpl_staged_spec_binder b in *)
      (* TFun b *)
  | TBinop _ -> t
  | TUnop _ -> t
and simpl_prop (p : prop) : prop = p
and simpl_hprop (p : hprop) : hprop = p

(** This is the entry point for [simpl].

    For simplicity, we only simplify [Sequence] and [Bind] at the moment. We do
    not simplify [Shift] and [Reset]. *)
let rec simpl_staged_spec (s : staged_spec) : staged_spec =
  match s with
  | Return t -> Return t
  | Requires p -> Requires p
  | Ensures p -> Ensures p
  | Sequence (s1, s2) -> simpl_staged_spec_cont s1 (CCons0 (s2, CNil))
  | Bind (s, b) -> simpl_staged_spec_cont s (CCons1 (b, CNil))
  | Apply (f, t) ->
      begin
        match f with
        | TFun b -> simpl_staged_spec (subst b t)
        | _ -> Apply (f, t)
      end
  | Disjunct (s1, s2) -> Disjunct (simpl_staged_spec s1, simpl_staged_spec s2)
  | Forall b -> Forall b
  | Exists b -> Exists b
  | Shift b -> Shift b
  | Reset s -> Reset (simpl_staged_spec s)
  | Dollar _ -> failwith "todo"
  (* | Dollar (s, k) -> simpl_staged_spec_cont s (CCons1 (k, CNil)) *)

and simpl_staged_spec_cont (s : staged_spec) (k : cont) : staged_spec =
  match s with
  | Return t -> simpl_invoke_cont k t
  | Requires p -> Sequence (Requires p, simpl_invoke_cont k TUnit)
  | Ensures p -> Sequence (Ensures p, simpl_invoke_cont k TUnit)
  | Sequence (s1, s2) -> simpl_staged_spec_cont s1 (CCons0 (s2, k))
  | Bind (s, b) -> simpl_staged_spec_cont s (CCons1 (b, k))
  | Apply (f, t) ->
      begin
        match f with
        | TFun b -> simpl_staged_spec_cont (subst b t) k
        | _ -> refine_cont (Apply (f, t)) k
      end
  | Disjunct (s1, s2) -> Disjunct (simpl_staged_spec_cont s1 k, simpl_staged_spec_cont s2 k)
  | Forall _ -> refine_cont s k
  | Exists _ -> refine_cont s k
  | Shift _ -> refine_cont s k
  | Reset s -> refine_cont (Reset (simpl_staged_spec s)) k
  | Dollar _ -> failwith "todo"

and simpl_invoke_cont (k : cont) (t : term) =
  match k with
  | CNil -> Return t
  | CCons0 (s, k) -> simpl_staged_spec_cont s k
  | CCons1 (b, k) -> simpl_staged_spec_cont (subst b t) k

(* TODO: do we simplify under binder? *)

(** This is the main entry point for [shift/reset reduction]. *)
let rec reduce_staged_spec (s : staged_spec) : staged_spec =
  match s with
  | Return t -> Return t
  | Requires p -> Requires p
  | Ensures p -> Ensures p
  | Sequence (s1, s2) -> Sequence (reduce_staged_spec s1, reduce_staged_spec s2)
  | Bind (s, b) -> Bind (reduce_staged_spec s, b)
  | Apply (f, t) -> Apply (f, t)
  | Disjunct (s1, s2) -> Disjunct (reduce_staged_spec s1, reduce_staged_spec s2)
  | Forall b -> Forall b
  | Exists b -> Exists b
  | Shift b -> Shift b
  | Reset s -> reduce_staged_spec_cont s CNil
  | Dollar _ -> failwith "todo"

(** This function is called only when we visit the body of a [Reset] during
    shift/reset reduction. *)
and reduce_staged_spec_cont (s : staged_spec) (k : cont) : staged_spec =
  match s with
  | Return t -> reduce_invoke_cont k t
  | Requires p -> Sequence (Requires p, reduce_invoke_cont k TUnit) (* Float requires outside of reset *)
  | Ensures p -> Sequence (Ensures p, reduce_invoke_cont k TUnit)
  | Sequence (s1, s2) -> reduce_staged_spec_cont s1 (CCons0 (s2, k))
  | Bind (s, b) -> reduce_staged_spec_cont s (CCons1 (b, k))
  | Apply (f, t) -> Reset (refine_cont (Apply (f, t)) k)
  | Disjunct (s1, s2) -> Disjunct (reduce_staged_spec_cont s1 k, reduce_staged_spec_cont s2 k)
  (* | Forall b -> ??? *)
  (* | Exists b -> ??? *)
  | Shift b -> reduce_staged_spec_cont (subst b (capture_cont k)) CNil
  | Reset s -> reduce_staged_spec_cont (reduce_staged_spec_cont s CNil) k
  | _ -> failwith "todo"

and reduce_invoke_cont (k : cont) (t : term) : staged_spec =
  match k with
  | CNil -> Return t
  | CCons0 (s, k) -> reduce_staged_spec_cont s k
  | CCons1 (b, k) -> reduce_staged_spec_cont (subst b t) k
