open Bindlib
open Core.Syntax

(* type quantifier =
  | QForall of term mvar
  | QExists of term mvar

(** A formula in prenex form, with quantifiers in outermost-first order. **)
type 'a prenex = {
  quantifiers : quantifier list;
  body : 'a;
}

let pure body = { quantifiers = []; body }
let prepend_quantifier q pf = { pf with quantifiers = q :: pf.quantifiers }

let combine f pf1 pf2 =
  {
    quantifiers = pf1.quantifiers @ pf2.quantifiers;
    body = f pf1.body pf2.body;
  }

let map f pf = { pf with body = f pf.body }

let rec close (pf : term Bindlib.box prenex) : term Bindlib.box =
  match pf.quantifiers with
  | [] -> pf.body
  | QForall x :: rest ->
      Mk.forall (bind_mvar x (close { quantifiers = rest; body = pf.body }))
  | QExists x :: rest ->
      Mk.exists (bind_mvar x (close { quantifiers = rest; body = pf.body }))

let close_unbox pf = unbox (close (map box_term pf)) *)

let rec prenex_box t =
  match t with
  | Forall b -> Mk.forall (prenex_box_mbinder b)
  | Exists b -> Mk.exists (prenex_box_mbinder b)
  | Sequence (t1, t2) -> prenex_box_cont t1 (fun tb -> Mk.sequence tb (box_term t2))
  | Bind (t, b) -> prenex_box_cont t (fun tb -> Mk.bind tb (box_binder box_term b))
  | _ -> box_term t

(** The continuation is necessary here, as we turn the quantifiers inside-out.
    It encodes how to construct the matrix inside the quantifiers. *)
and prenex_box_cont t k =
  match t with
  | Forall b -> Mk.forall (prenex_box_mbinder_cont b k)
  | Exists b -> Mk.exists (prenex_box_mbinder_cont b k)
  | Sequence (t1, t2) -> prenex_box_cont t1 (fun tb -> k (Mk.sequence tb (box_term t2)))
  | Bind (t, b) -> prenex_box_cont t (fun tb -> k (Mk.bind tb (box_binder box_term b)))
  | _ -> k (box_term t)

and prenex_box_mbinder b =
  let xs, t = unmbind b in
  bind_mvar xs (prenex_box t)

and prenex_box_mbinder_cont b k =
  let xs, t = unmbind b in
  bind_mvar xs (prenex_box_cont t k)

let prenex t = unbox (prenex_box t)


(* let rec prenex_term (t : term) : term prenex =
  match t with
  (* Atomic / Pure terms *)
  | Var _ | Symbol _ | Unit | True | False | Int _ | Nil | Emp -> pure t
  | Tuple ts ->
      let ts' = List.map process_term ts in
      pure (Tuple ts')
  | Binop (op, t1, t2) -> pure (Binop (op, process_term t1, process_term t2))
  | Unop (op, t) -> pure (Unop (op, process_term t))
  | PointsTo (t1, t2) -> pure (PointsTo (process_term t1, process_term t2))
  | SepConj (h1, h2) -> pure (SepConj (process_term h1, process_term h2))
  | Conj (p1, p2) -> pure (Conj (process_term p1, process_term p2))
  | Implies (p1, p2) -> pure (Implies (process_term p1, process_term p2))
  | Subsumes (s1, s2) -> pure (Subsumes (process_term s1, process_term s2))
  (* Recursive / Scope handling *)
  | Fun b ->
      let xs, body = unmbind b in
      let body' = process_term body in
      pure (unbox (Mk.fun_ (bind_mvar xs (box_term body'))))
  | Apply (f, ts) -> pure (Apply (process_term f, List.map process_term ts))
  (* Spec / Logic control flow *)
  | Requires h -> pure (Requires (process_term h))
  | Ensures h -> pure (Ensures (process_term h))
  | Sequence (s1, s2) ->
      combine (fun b1 b2 -> Sequence (b1, b2)) (prenex_term s1) (prenex_term s2)
  | Bind (s1, b) ->
      let pf1 = prenex_term s1 in
      let x, s2 = unbind b in
      let pf2 = prenex_term s2 in
      let new_body =
        unbox (Mk.bind (box_term pf1.body) (bind_var x (box_term pf2.body)))
      in
      { quantifiers = pf1.quantifiers @ pf2.quantifiers; body = new_body }
  | Disj (s1, s2) ->
      combine (fun b1 b2 -> Disj (b1, b2)) (prenex_term s1) (prenex_term s2)
  | Forall b ->
      let x, body = unmbind b in
      prepend_quantifier (QForall x) (prenex_term body)
  | Exists b ->
      let x, body = unmbind b in
      prepend_quantifier (QExists x) (prenex_term body)
  | Shift b ->
      let x, body = unbind b in
      let body' = process_term body in
      pure (unbox (Mk.shift (bind_var x (box_term body'))))
  | Reset s1 -> pure (Reset (process_term s1))

and process_term t = close_unbox (prenex_term t)

let move_quantifiers_out s = process_term s *)
