open Bindlib
open Core.Syntax

let rec box_prenex t =
  match t with
  | Forall b -> Mk.forall (box_prenex_mbinder b)
  | Exists b -> Mk.exists (box_prenex_mbinder b)
  | Sequence (t1, t2) -> box_prenex_cont t1 (fun tb -> Mk.sequence tb (box_term t2))
  | Bind (t, b) -> box_prenex_cont t (fun tb -> Mk.bind tb (box_binder box_term b))
  | _ -> box_term t

(** The continuation is necessary here, as we turn the quantifiers inside-out.
    It encodes how to construct the matrix inside the quantifiers. *)
and box_prenex_cont t k =
  match t with
  | Forall b -> Mk.forall (box_prenex_mbinder_cont b k)
  | Exists b -> Mk.exists (box_prenex_mbinder_cont b k)
  | Sequence (t1, t2) -> box_prenex_cont t1 (fun tb -> k (Mk.sequence tb (box_term t2)))
  | Bind (t, b) -> box_prenex_cont t (fun tb -> k (Mk.bind tb (box_binder box_term b)))
  | _ -> k (box_term t)

and box_prenex_mbinder b =
  let xs, t = unmbind b in
  bind_mvar xs (box_prenex t)

and box_prenex_mbinder_cont b k =
  let xs, t = unmbind b in
  bind_mvar xs (box_prenex_cont t k)

let prenex t = unbox (box_prenex t)
