open Bindlib
open Core.Syntax

type quantifier =
  | QForall of term mvar
  | QExists of term mvar

(** A formula in prenex form, with quantifiers in outermost-first order. *)
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

let rec close (pf : staged_spec Bindlib.box prenex) : staged_spec Bindlib.box =
  match pf.quantifiers with
  | [] -> pf.body
  | QForall x :: rest ->
    Mk.forall (bind_mvar x (close { quantifiers = rest; body = pf.body }))
  | QExists x :: rest ->
    Mk.exists (bind_mvar x (close { quantifiers = rest; body = pf.body }))

let close_unbox pf = unbox (close (map box_staged_spec pf))

let rec prenex_term (t : term) : term =
  match t with
  | Var _ | Symbol _ | Unit | True | False | Int _ | Nil -> t
  | Fun b ->
    let xs, body = unmbind b in
    let body' = close_unbox (prenex_term body) in
    unbox (Mk.fun_ (bind_mvar xs (box_staged_spec body')))
  | Apply (f, ts) -> Apply (f, List.map prenex_term ts)
  | Tuple ts -> Tuple (List.map prenex_term ts)
  | Binop (op, t1, t2) -> Binop (op, prenex_term t1, prenex_term t2)
  | Unop (op, t) -> Unop (op, prenex_term t)
  (* | Emp
  | Conj (_, _)
  | Disj (_, _)
  | Implies (_, _)
  | Subsumes (_, _)
  | PointsTo (_, _)
  | SepConj (_, _)
  | Requires _ | Ensures _
  | Sequence (_, _)
  | Bind (_, _)
  | Forall _ | Exists _ | Shift _ | Reset _ ->
    assert false *)
  (* and prenex_term (p : prop) : prop = *)
  (* match p with *)
  | Conj (p1, p2) -> Conj (prenex_term p1, prenex_term p2)
  | Implies (p1, p2) -> Implies (prenex_term p1, prenex_term p2)
  | Forall b ->
    let x, body = unmbind b in
    let body' = prenex_term body in
    unbox (Mk.forall (bind_mvar x (box_prop body')))
  | Subsumes (s1, s2) ->
    Subsumes (close_unbox (prenex_term s1), close_unbox (prenex_term s2))
  (* | _ -> assert false *)
  (*
and prenex_term (h : hprop) : hprop =
  match h with *)
  | Emp -> Emp
  | PointsTo (t1, t2) -> PointsTo (prenex_term t1, prenex_term t2)
  | SepConj (h1, h2) -> SepConj (prenex_term h1, prenex_term h2)
  (* | _ -> assert false

and prenex_term (s : staged_spec) : staged_spec prenex =
  match s with *)
  (* | Return t -> pure (Return (prenex_term t)) *)
  | Requires h -> pure (Requires (prenex_term h))
  | Ensures h -> pure (Ensures (prenex_term h))
  | Apply (t1, t2) -> pure (Apply (prenex_term t1, List.map prenex_term t2))
  | Sequence (s1, s2) ->
    combine (fun b1 b2 -> Sequence (b1, b2)) (prenex_term s1) (prenex_term s2)
  | Bind (s1, b) ->
    let pf1 = prenex_term s1 in
    let x, s2 = unbind b in
    let pf2 = prenex_term s2 in
    let new_body =
      unbox
        (Mk.bind (box_staged_spec pf1.body)
           (bind_var x (box_staged_spec pf2.body)))
    in
    { quantifiers = pf1.quantifiers @ pf2.quantifiers; body = new_body }
  | Disjunct (s1, s2) ->
    combine (fun b1 b2 -> Disjunct (b1, b2)) (prenex_term s1) (prenex_term s2)
  | Forall b ->
    let x, body = unmbind b in
    prepend_quantifier (QForall x) (prenex_term body)
  | Exists b ->
    let x, body = unmbind b in
    prepend_quantifier (QExists x) (prenex_term body)
  | Shift b ->
    let x, body = unbind b in
    let body' = close_unbox (prenex_term body) in
    pure (unbox (Mk.shift (bind_var x (box_staged_spec body'))))
  | Reset s1 -> pure (Reset (close_unbox (prenex_term s1)))
  | Dollar (s1, b) ->
    let x, s2 = unbind b in
    let s1' = close_unbox (prenex_term s1) in
    let s2' = close_unbox (prenex_term s2) in
    pure
      (unbox
         (Mk.dollar (box_staged_spec s1') (bind_var x (box_staged_spec s2'))))

let move_quantifiers_out s = s |> prenex_term |> close_unbox

let%expect_test "prenex" =
  let test s =
    let f = Parsing.Parse.parse_staged_spec s in
    let f1 = move_quantifiers_out f in
    Format.printf "%a@." Core.Pretty.pp_staged_spec f1
  in
  test "ens emp; r. ex a. ens a=1";
  [%expect {| ex a. ens emp; r. ens a=1 |}];

  test "ens emp; r. (forall a. ens a=1 \\/ ens emp)";
  [%expect {| forall a. ens emp; r. (ens a=1 \/ ens emp) |}];

  (* quantifiers don't get lifted out of a reset *)
  test "reset (forall a. ens a=1)";
  [%expect {| reset (forall a. ens a=1) |}];

  (* prop also contains forall *)
  test "ens emp; r. ens forall a. a=1";
  [%expect {| ens emp; r. ens forall a. a=1 |}]
