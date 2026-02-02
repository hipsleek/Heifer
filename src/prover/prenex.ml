open Bindlib
open Core.Syntax

let rec box_prenex_head t =
  match t with
  | Forall b -> Mk.forall (box_prenex_head_mbinder b)
  | Exists b -> Mk.exists (box_prenex_head_mbinder b)
  | Sequence (t1, t2) -> box_prenex_head_cont t1 (fun tb -> Mk.sequence tb (box_term t2))
  | Bind (t, b) -> box_prenex_head_cont t (fun tb -> Mk.bind tb (box_binder box_term b))
  | _ -> box_term t

(** The continuation is necessary here, as we turn the quantifiers inside-out.
    It encodes how to construct the matrix inside the quantifiers. *)
and box_prenex_head_cont t k =
  match t with
  | Forall b -> Mk.forall (box_prenex_head_mbinder_cont b k)
  | Exists b -> Mk.exists (box_prenex_head_mbinder_cont b k)
  | Sequence (t1, t2) -> box_prenex_head_cont t1 (fun tb -> k (Mk.sequence tb (box_term t2)))
  | Bind (t, b) -> box_prenex_head_cont t (fun tb -> k (Mk.bind tb (box_binder box_term b)))
  | _ -> k (box_term t)

and box_prenex_head_mbinder b =
  let xs, t = unmbind b in
  bind_mvar xs (box_prenex_head t)

and box_prenex_head_mbinder_cont b k =
  let xs, t = unmbind b in
  bind_mvar xs (box_prenex_head_cont t k)

let prenex_head t = unbox (box_prenex_head t)


(* Prenex, on the entire formula *)
let rec box_prenex_assoc t =
  match t with
  | Conj (t1, t2) -> Mk.conj (box_prenex_assoc t1) (box_prenex_assoc t2)
  | Disj (t1, t2) -> Mk.disj (box_prenex_assoc t1) (box_prenex_assoc t2)
  | Forall b -> Mk.forall (box_prenex_assoc_mbinder b)
  | Exists b -> Mk.exists (box_prenex_assoc_mbinder b)
  | Shift b -> Mk.shift (box_prenex_assoc_binder b)
  | Reset t -> Mk.reset (box_prenex_assoc t)
  | Sequence (t1, t2) -> box_prenex_assoc_cont t1 (fun tb -> Mk.sequence tb (box_prenex_assoc t2))
  | Bind (t, b) -> box_prenex_assoc_cont t (fun tb -> Mk.bind tb (box_prenex_assoc_binder b))
  | Subsumes (t1, t2) -> Mk.subsumes (box_prenex_assoc t1) (box_prenex_assoc t2)
  | _ -> box_term t

and box_prenex_assoc_cont t k =
  match t with
  (* | Conj (t1, t2) -> Mk.conj (box_prenex_assoc_cont t1 k) (box_prenex_assoc_cont t2 k) *)
  | Conj (t1, t2) -> k (Mk.conj (box_prenex_assoc t1) (box_prenex_assoc t2))
  | Disj (t1, t2) -> Mk.disj (box_prenex_assoc_cont t1 k) (box_prenex_assoc_cont t2 k)
  | Forall b -> Mk.forall (box_prenex_assoc_mbinder_cont b k)
  | Exists b -> Mk.exists (box_prenex_assoc_mbinder_cont b k)
  | Shift b -> k (Mk.shift (box_prenex_assoc_binder b))
  | Reset t -> k (Mk.reset (box_prenex_assoc t))
  | Sequence (t1, t2) -> box_prenex_assoc_cont t1 (fun tb -> Mk.sequence tb (box_prenex_assoc_cont t2 k))
  | Bind (t, b) -> box_prenex_assoc_cont t (fun tb -> Mk.bind tb (box_prenex_assoc_binder_cont b k))
  | _ -> k (box_term t)

and box_prenex_assoc_binder b =
  let x, t = unbind b in
  bind_var x (box_prenex_assoc t)

and box_prenex_assoc_binder_cont b k =
  let x, t = unbind b in
  bind_var x (box_prenex_assoc_cont t k)

and box_prenex_assoc_mbinder b =
  let xs, t = unmbind b in
  bind_mvar xs (box_prenex_assoc t)

and box_prenex_assoc_mbinder_cont b k =
  let xs, t = unmbind b in
  bind_mvar xs (box_prenex_assoc_cont t k)

let prenex_assoc t = unbox (box_prenex_assoc t)
