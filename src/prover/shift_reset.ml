open Bindlib
open Core.Syntax
open Core.Pretty

type cont =
  | Nil
  | Cons_sequence of term * cont
  | Cons_bind of (term, term) binder * cont

let rec box_refine_box_cont tb = function
  | Nil -> tb
  | Cons_sequence (t, k) -> Mk.sequence tb (box_refine_cont t k)
  | Cons_bind (b, k) ->
      let x, t = unbind b in
      Mk.bind tb (bind_var x (box_refine_cont t k))

and box_refine_cont t = box_refine_box_cont (box_term t)

let box_refine_cont_reset t k = Mk.reset (box_refine_cont t k)

let refine_cont t k = unbox (box_refine_cont t k)

let refine_cont_reset t k = Reset (refine_cont t k)

let ignored_tvar = new_tvar "_"

let captured_nil =
  let x = new_tvar "x" in
  unbox (Mk.fun_ (bind_mvar [| x |] (Mk.var x)))

let capture_cont = function
  | Nil -> captured_nil
  | Cons_sequence (t, k) -> unbox (Mk.fun_ (bind_mvar [| ignored_tvar |] (box_refine_cont_reset t k)))
  | Cons_bind (b, k) ->
      let x, t = unbind b in
      unbox (Mk.fun_ (bind_mvar [| x |] (box_refine_cont_reset t k)))

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
  | Requires _ -> invoke_cont_impure_unit t k
  | Ensures _ -> invoke_cont_impure_unit t k
  | Sequence (t1, t2) -> reduce_cont t1 (Cons_sequence (t2, k))
  | Bind (t, b) -> reduce_cont t (Cons_bind (b, k))
  | Apply _ -> refine_cont_reset t k
  | Disj (t1, t2) -> Disj (reduce_cont t1 k, reduce_cont t2 k)
  | Forall b -> Reset (refine_cont (Forall (reduce_mbinder b)) k)
  | Exists b -> Reset (refine_cont (Exists (reduce_mbinder b)) k)
  | Shift b -> reduce_cont (subst b (capture_cont k)) Nil
  | Reset t -> reduce_cont (reduce_cont t Nil) k
  | Unit
  | True
  | False
  | Int _
  | Fun _
  | Binop _
  | Unop _
  | Tuple _ 
  | Nil -> invoke_cont_pure t k
  | _ -> invalid_arg (Format.asprintf "reduce_cont: %a" pp_term t)

and invoke_cont_pure t = function
  | Nil -> t
  | Cons_sequence (t', k) -> reduce_cont t' k
  | Cons_bind (b, k) -> reduce_cont (subst b t) k

and invoke_cont_impure_unit t = function
  | Nil -> t
  | Cons_sequence (t', k) -> Sequence (t, reduce_cont t' k)
  | Cons_bind (b, k) -> Sequence (t, reduce_cont (subst b Unit) k)
