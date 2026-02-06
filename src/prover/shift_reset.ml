open Bindlib
open Core.Syntax
open Core.Syntax_util
open Cont

(** This is the main entry point for [shift/reset reduction]. *)
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
  | Reset t -> reduce_cont t Nil
  | Subsumes (t1, t2) -> Subsumes (reduce t1, reduce t2)
  | _ -> t

and reduce_binder b =
  let x, t = unbind b in
  generalize x (reduce t)

and reduce_mbinder b =
  let xs, t = unmbind b in
  mgeneralize xs (reduce t)

(** This function is called only when we visit the body of a [Reset] during shift/reset reduction.
*)
and reduce_cont t k =
  match t with
  | Requires _ -> invoke_cont_impure_unit t k
  | Ensures _ -> invoke_cont_impure_unit t k
  | Sequence (t1, t2) -> reduce_cont t1 (Cons_sequence (t2, k))
  | Bind (t, b) -> reduce_cont t (Cons_bind (b, k))
  | Apply _ -> refine_cont_reset t k
  | Disj (t1, t2) -> Disj (reduce_cont t1 k, reduce_cont t2 k)
  | Forall b -> Forall (reduce_mbinder_cont b k)
  | Exists b -> Exists (reduce_mbinder_cont b k)
  | Shift b -> reduce_cont (subst b (capture_cont_reset k)) Nil
  | Reset t ->
      let t = reduce_cont t Nil in
      if is_reset t then invoke_cont_impure t k else reduce_cont t k
  | Var _
  | Symbol _
  | OSome _
  | ONone
  | Unit
  | True
  | False
  | Int _
  | Fun _
  | Binop _
  | Unop _
  | Tuple _
  | Nil
  | Conj _ -> invoke_cont_pure t k
  | _ -> invalid_arg (Format.asprintf "reduce_cont: %a" dump_term t)

and reduce_binder_cont b k =
  let x, t = unbind b in
  generalize x (reduce_cont t k)

and reduce_mbinder_cont b k =
  let xs, t = unmbind b in
  mgeneralize xs (reduce_cont t k)

and invoke_cont_pure t = function
  | Nil -> t
  | Cons_sequence (t, k) -> reduce_cont t k
  | Cons_bind (b, k) -> reduce_cont (subst b t) k

and invoke_cont_impure_unit t = function
  | Nil -> t
  | Cons_sequence (t', k) -> Sequence (t, reduce_cont t' k)
  | Cons_bind (b, k) -> Sequence (t, reduce_cont (subst b Unit) k)

and invoke_cont_impure t = function
  | Nil -> t
  | Cons_sequence (t', k) -> Sequence (t, reduce_cont t' k)
  | Cons_bind (b, k) -> Bind (t, reduce_binder_cont b k)
