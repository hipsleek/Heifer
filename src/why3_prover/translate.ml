open Why3
open Core.Syntax
open Ptree
open Ptree_helpers

let rec is_translatable t =
  match t with
  | Symbol _ | Var _ | True | False -> true (* atomic propositions *)
  | Unit | Nil | Emp | Int _ | Tuple _ -> true (* term *)
  | Binop ((Lt | Le | Gt | Ge | Eq | Neq | Plus | Minus | Times | Cons), t1, t2) ->
      is_translatable t1 && is_translatable t2
  | Unop ((Not | Neg), t) -> is_translatable t
  | Forall b | Exists b -> is_translatable_mbinder b
  | Apply (t, ts) -> is_translatable t && is_translatable_list ts
  | Conj (t1, t2) | Disj (t1, t2) | Implies (t1, t2) ->
      is_translatable t1 && is_translatable t2
  | Sequence (t1, t2) -> is_translatable t1 && is_translatable t2
  | Bind (t, b) -> is_translatable t && is_translatable_binder b
      (* staged logic and separation logic can't be translated *)
  | Fun _ | Requires _ | Ensures _ | Subsumes _
  | PointsTo _ | SepConj _ | Wand _ | Shift _ | Reset _ -> false

and is_translatable_list ts =
  List.for_all is_translatable ts

and is_translatable_binder b =
  let _, t = Bindlib.unbind b in
  is_translatable t

and is_translatable_mbinder b =
  let _, t = Bindlib.unmbind b in
  is_translatable t

let var_to_param x =
  Loc.dummy_position, Some (ident x), false, Some (PTtyapp (qualid ["term"], []))

let vars_to_params = List.map var_to_param

type kind =
  | Formula
  | Term

let coerce_to_prop t =
  tapp (qualid [Ident.op_infix "="]) [t; tapp (qualid ["TBool"]) [term Ttrue]]

(** Implemented cases should be kept in sync with [is_translatable].

    This translation is contetxtual: it depends on what the expected type of the
    context (initially Formula) is. We need this because we model both terms and
    props (called "formula" in Why3) in one type (due to allowing props to
    appear inside terms), whereas Why3 separates them.

    This translation assumes that propos do not appear in terms (i.e. once the
    context type becomes Term, it never changes back to Formula), as that's
    supposed to be handled by the staged logic prover. *)
let rec term_to_whyml_aux ctxt kind t =
  (* let s =
    match kind with
    | Formula -> "formula"
    | Term -> "term"
  in
  Format.printf "%a %s@." Core.Pretty.pp_term t s; *)
  match (t, kind) with
  | Unit, Term ->
      (* term (Ttuple []) *)
      tvar (qualid ["TUnit"])
  | Unit, Formula -> failwith "unit cannot be used as a formula"
  | True, Term -> tapp (qualid ["TBool"]) [term Ttrue]
  | False, Term -> tapp (qualid ["TBool"]) [term Tfalse]
  | True, Formula -> term Ttrue
  | False, Formula -> term Tfalse
  | Nil, Term ->
      (* tapp (qualid ["TNil"]) []  *)
      tvar (qualid ["TNil"])
  | Nil, Formula -> failwith "nil cannot be used as a formula"
  | Int i, Term -> tapp (qualid ["TInt"]) [tconst i]
  | Int _, Formula -> failwith "int cannot be used as a formula"
  | Binop (Times, a, b), Term ->
      tapp (qualid ["times"])
        (* (qualid ["Int"; Ident.op_infix "*"]) *)
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Plus, a, b), Term ->
      (* tapp (qualid ["Int"; Ident.op_infix "+"]) [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b] *)
      tapp (qualid ["plus"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Minus, a, b), Term ->
      tapp (qualid ["minus"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Cons, h, t), Term ->
      tapp (qualid ["TCons"])
        [term_to_whyml_aux ctxt Term h; term_to_whyml_aux ctxt Term t]
  | Binop ((Times | Plus | Minus | Cons), _, _), Formula ->
      failwith "binop cannot be used as a formula"
  | Unop (Not, a), Formula -> term (Tnot (term_to_whyml_aux ctxt Formula a))
  | Unop (Not, a), Term -> tapp (qualid ["Bool"; "notb"]) [term_to_whyml_aux ctxt Term a]
  | Unop (Neg, t), Term -> tapp (qualid ["neg"]) [term_to_whyml_aux ctxt Term t]
  | Unop (Neg, _), Formula -> failwith "neg cannot be used as a formula"
  | Var x, _ ->
      (* tapp (qualid ["Var"]) [tstr (Bindlib.name_of x)] *)
      tvar (qualid [Bindlib.name_of x])
  | Symbol { sym_name }, Term -> tvar (qualid [sym_name])
  | Symbol _, Formula -> failwith "symbol cannot be used as formula"
  | Fun _, _ -> failwith "lambdas not handled at this level"
  | Tuple _, Term -> failwith "todo tuple"
  | Tuple _, Formula -> failwith "tuple cannot be used as a formula"
  (* | Apply (Symbol { sym_name = "is_int" }, args), Formula ->
      tapp (qualid ["is_int"]) (List.map (term_to_whyml_aux ctxt Term) args) *)
  | Apply (Symbol { sym_name = f }, args), _ ->
      tapp (qualid [f]) (List.map (term_to_whyml_aux ctxt Term) args)
  | Apply (_f, _args), _ -> failwith "apply"
  | Sequence (_, t), Term -> term_to_whyml_aux ctxt Term t
  | Sequence _, Formula -> failwith "sequence cannot be used in a formula"
  | Bind (t, b), Term ->
      (* there is no let in whyml terms, only programs... *)
      (* let x, b, ctxt = Bindlib.unbind_in ctxt b in
      term
        (Tlet
           ( ident (Bindlib.name_of x),
             term_to_whyml_aux ctxt a,
             term_to_whyml_aux ctxt b )) *)
      term_to_whyml_aux ctxt Term (Bindlib.subst b t)
  | Bind _, Formula -> failwith "bind cannot be used in a formula"
  | Forall b, Formula ->
      let xs, b, ctxt = Bindlib.unmbind_in ctxt b in
      let xs = Array.to_list xs |> List.map Bindlib.name_of in
      term
        (Tquant
           ( Dterm.DTforall,
             vars_to_params xs,
             [],
             term_to_whyml_aux ctxt Formula b ))
  | Exists b, Formula ->
      let xs, b, ctxt = Bindlib.unmbind_in ctxt b in
      let xs = Array.to_list xs |> List.map Bindlib.name_of in
      term
        (Tquant
           ( Dterm.DTexists,
             vars_to_params xs,
             [],
             term_to_whyml_aux ctxt Formula b ))
  | (Forall _ | Exists _), Term ->
      failwith "quantifiers cannot be used as a term"
  | Binop (Eq, a, b), Term ->
      tapp
        (* (qualid [Ident.op_infix "="]) *)
        (qualid ["eq"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Gt, a, b), Term ->
      tapp (qualid ["gt"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Lt, a, b), Term ->
      tapp (qualid ["lt"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Le, a, b), Term ->
      tapp (qualid ["le"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Ge, a, b), Term ->
      tapp (qualid ["ge"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Neq, a, b), Term ->
      tapp (qualid ["neq"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Eq, a, b), Formula ->
      tapp
        (qualid [Ident.op_infix "="])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop (Neq, a, b), Formula ->
      tapp
        (qualid [Ident.op_infix "<>"])
        [term_to_whyml_aux ctxt Term a; term_to_whyml_aux ctxt Term b]
  | Binop ((Gt | Lt | Le | Ge), _, _), Formula ->
      coerce_to_prop (term_to_whyml_aux ctxt Term t)
  | Conj (t1, t2), Term ->
      tapp (qualid ["and"]) [term_to_whyml_aux ctxt Term t1; term_to_whyml_aux ctxt Term t2]
  | Conj (t1, t2), Formula ->
      term (Tbinop (term_to_whyml_aux ctxt kind t1, Dterm.DTand, term_to_whyml_aux ctxt kind t2))
  | Disj (t1, t2), Term ->
      tapp (qualid ["or"]) [term_to_whyml_aux ctxt Term t1; term_to_whyml_aux ctxt Term t2]
  | Disj (t1, t2), Formula ->
      term (Tbinop (term_to_whyml_aux ctxt kind t1, Dterm.DTor, term_to_whyml_aux ctxt kind t2))
  | Implies (t1, t2), Term ->
      let t1 = term_to_whyml_aux ctxt Term t1 in
      let t2 = term_to_whyml_aux ctxt Term t2 in
      tapp (qualid ["implies"]) [t1; t2]
  | Implies (t1, t2), Formula ->
      let t1 = term_to_whyml_aux ctxt Formula t1 in
      let t2 = term_to_whyml_aux ctxt Formula t2 in
      term (Tbinop (t1, Dterm.DTimplies, t2))
  | Emp, _ | PointsTo _, _ | SepConj _, _ | Wand _, _ ->
      failwith "separation logic cannot be translated"
  | Subsumes _, _ -> failwith "subsumptions not handled at this level"
  | Requires _, _ | Ensures _, _ | Shift _, _ | Reset _, _ ->
      failwith "staged logic not handled at this level"

let term_to_whyml p =
  term_to_whyml_aux Bindlib.(free_vars (box_term p)) Formula p
