open Bindlib
open Core.Syntax
open Core.Pretty

type cont =
  | Nil
  | Cons_sequence of term * cont
  | Cons_bind of (term, term) binder * cont

let rec refineb_box_cont tb = function
  | Nil -> tb
  | Cons_sequence (t, k) -> Mk.sequence tb (refineb_cont t k)
  | Cons_bind (b, k) ->
      let x, t = unbind b in
      Mk.bind tb (bind_var x (refineb_cont t k))

and refineb_cont t = refineb_box_cont (box_term t)

let refine_cont t k = unbox (refineb_cont t k)

(* let rec refine_cont (t : term) (k : cont) : term =
  match k with
  | CNil -> t
  | CCons0 (t', k) -> Sequence (t, refine_cont t' k)
  | CCons1 (b, k) ->
      let x, t' = unbind b in
      Bind (t, unbox (bind_var x (box_term (refine_cont t' k)))) *)

(* let capture_cont (k : cont) : term =
  match k with
  | CNil ->
      let x = new_tvar "x" in
      unbox (Mk.fun_ (bind_mvar [| x |] (Mk.var x)))
  | CCons0 (t, k) ->
      let x = new_tvar "_" in
      unbox (Mk.fun_ (bind_mvar [| x |] (box_term (Reset (refine_cont t k)))))
  | CCons1 (b, k) ->
      let x, t = unbind b in
      unbox (Mk.fun_ (bind_mvar [| x |] (box_term (Reset (refine_cont t k))))) *)

(** This is the main entry point for [shift/reset reduction].

    TODO: rewrite this. *)
let rec reduce t =
  match t with
  | Requires t -> Requires t
  | Ensures t -> Ensures t
  | Sequence (t1, t2) -> Sequence (reduce t1, reduce t2)
  | Bind (t, b) -> Bind (reduce t, reduce_binder b)
  | Apply (t, ts) -> Apply (t, ts)
  | Conj (t1, t2) -> Conj (reduce t1, reduce t2)
  | Disj (t1, t2) -> Disj (reduce t1, reduce t2)
  | Forall b -> Forall (reduce_mbinder b)
  | Exists b -> Exists (reduce_mbinder b)
  | Shift b -> Shift (reduce_binder b)
  | Reset _t -> failwith "todo"
  | Subsumes (t1, t2) -> Subsumes (reduce t1, reduce t2)
  | _ -> t

and reduce_binder b =
  let x, t = unbind b in
  unbox (bind_var x (box_term (reduce t)))

and reduce_mbinder b =
  let xs, t = unmbind b in
  unbox (bind_mvar xs (box_term (reduce t)))

(** This function is called only when we visit the body of a [Reset] during
    shift/reset reduction. *)
and reduce_cont t k =
  match t with
  | Requires p ->
      Sequence (Requires p, reduce_invoke_cont k Unit)
      (* Float requires outside of reset *)
  | Ensures p -> Sequence (Ensures p, reduce_invoke_cont k Unit)
  | Sequence (t1, t2) -> reduce_cont t1 (Cons_sequence (t2, k))
  | Bind (t, b) -> reduce_cont t (Cons_bind (b, k))
  | Apply _ -> Reset (refine_cont t k)
  | Disj (t1, t2) -> Disj (reduce_cont t1 k, reduce_cont t2 k)
  | Forall b -> Reset (refine_cont (Forall (reduce_mbinder b)) k)
  | Exists b -> Reset (refine_cont (Exists (reduce_mbinder b)) k)
  (* | Shift b -> reduce_cont (subst b (capture_cont k)) CNil
  | Reset t -> reduce_cont (reduce_cont t CNil) k *)
  | Subsumes _ -> invalid_arg (Format.asprintf "reduce_cont: %a" pp_term t)
  | _ -> reduce_invoke_cont k t

and reduce_invoke_cont (k : cont) (t : term) : term =
  ignore (k, t);
  failwith "todo"
  (* match k with
  | CNil -> t
  | CCons0 (t, k) -> reduce_cont t k
  | CCons1 (b, k) -> reduce_cont (subst b t) k *)
