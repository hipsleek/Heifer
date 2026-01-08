open Bindlib
open Core.Syntax

type quantifier =
  | QForall of term var
  | QExists of term var

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
    Mk.forall (bind_var x (close { quantifiers = rest; body = pf.body }))
  | QExists x :: rest ->
    Mk.exists (bind_var x (close { quantifiers = rest; body = pf.body }))

let close_unbox pf = unbox (close (map box_staged_spec pf))

let rec prenex_term (t : term) : term =
  match t with
  | TVar _ | TSymbol _ | TUnit | TTrue | TFalse | TInt _ | TNil -> t
  | TFun b ->
    let x, body = unbind b in
    let body' = close_unbox (prenex_staged_spec body) in
    unbox (Mk.tfun (bind_var x (box_staged_spec body')))
  | TApp (f, ts) -> TApp (f, List.map prenex_term ts)
  | TTuple ts -> TTuple (List.map prenex_term ts)
  | TBinop (op, t1, t2) -> TBinop (op, prenex_term t1, prenex_term t2)
  | TUnop (op, t) -> TUnop (op, prenex_term t)

and prenex_prop (p : prop) : prop =
  match p with
  | PAtom t -> PAtom (prenex_term t)
  | PConj (p1, p2) -> PConj (prenex_prop p1, prenex_prop p2)
  | PImplies (p1, p2) -> PImplies (prenex_prop p1, prenex_prop p2)
  | PForall b ->
    let x, body = unbind b in
    let body' = prenex_prop body in
    unbox (Mk.pforall (bind_var x (box_prop body')))
  | PSubsumes (s1, s2) ->
    PSubsumes
      (close_unbox (prenex_staged_spec s1), close_unbox (prenex_staged_spec s2))

and prenex_hprop (h : hprop) : hprop =
  match h with
  | HPure p -> HPure (prenex_prop p)
  | HEmp -> HEmp
  | HPointsTo (t1, t2) -> HPointsTo (prenex_term t1, prenex_term t2)
  | HSepConj (h1, h2) -> HSepConj (prenex_hprop h1, prenex_hprop h2)

and prenex_staged_spec (s : staged_spec) : staged_spec prenex =
  match s with
  | Return t -> pure (Return (prenex_term t))
  | Requires h -> pure (Requires (prenex_hprop h))
  | Ensures h -> pure (Ensures (prenex_hprop h))
  | Apply (t1, t2) -> pure (Apply (prenex_term t1, prenex_term t2))
  | Sequence (s1, s2) ->
    combine
      (fun b1 b2 -> Sequence (b1, b2))
      (prenex_staged_spec s1) (prenex_staged_spec s2)
  | Bind (s1, b) ->
    let pf1 = prenex_staged_spec s1 in
    let x, s2 = unbind b in
    let pf2 = prenex_staged_spec s2 in
    let new_body =
      unbox
        (Mk.bind (box_staged_spec pf1.body)
           (bind_var x (box_staged_spec pf2.body)))
    in
    { quantifiers = pf1.quantifiers @ pf2.quantifiers; body = new_body }
  | Disjunct (s1, s2) ->
    combine
      (fun b1 b2 -> Disjunct (b1, b2))
      (prenex_staged_spec s1) (prenex_staged_spec s2)
  | Forall b ->
    let x, body = unbind b in
    prepend_quantifier (QForall x) (prenex_staged_spec body)
  | Exists b ->
    let x, body = unbind b in
    prepend_quantifier (QExists x) (prenex_staged_spec body)
  | Shift b ->
    let x, body = unbind b in
    let body' = close_unbox (prenex_staged_spec body) in
    pure (unbox (Mk.shift (bind_var x (box_staged_spec body'))))
  | Reset s1 -> pure (Reset (close_unbox (prenex_staged_spec s1)))
  | Dollar (s1, b) ->
    let x, s2 = unbind b in
    let s1' = close_unbox (prenex_staged_spec s1) in
    let s2' = close_unbox (prenex_staged_spec s2) in
    pure
      (unbox
         (Mk.dollar (box_staged_spec s1') (bind_var x (box_staged_spec s2'))))

let move_quantifiers_out s = s |> prenex_staged_spec |> close_unbox

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
