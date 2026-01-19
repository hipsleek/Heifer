open Why3
open Core.Syntax
open Ptree
open Ptree_helpers

let rec is_translatable t =
  match t with
  | Symbol _ | Var _ | True | False ->
      (* atomic propositions *)
      true
  | Unit | Nil | Emp | Int _ | Tuple _ ->
      (* terms are fine too *)
      true
  | Binop ((Lt | Le | Gt | Ge | Eq | Neq | Plus | Minus | Times | Cons), a, b)
    -> is_translatable a && is_translatable b
  | Unop ((Not | Neg), a) -> is_translatable a (* terms *)
  | Forall b | Exists b ->
      let _, b = Bindlib.unmbind b in
      is_translatable b
  | Apply (a, b) -> is_translatable a && List.for_all is_translatable b
  | Conj (a, b) | Disj (a, b) | Implies (a, b) ->
      is_translatable a && is_translatable b
  (* somewhat unintuitively, bind is okay, but sequence is not, even though technically sequence is a special case of bind *)
  | Sequence _ -> false
  | Bind (a, b) ->
      let _, b = Bindlib.unbind b in
      is_translatable a && is_translatable b
      (* staged logic and separation logic can't be translated *)
  | Fun _ | Requires _ | Ensures _ | Subsumes _ -> false
  | PointsTo _ | SepConj _ | Shift _ | Reset _ -> false

let vars_to_params vars =
  List.map
    (fun v ->
      ( Loc.dummy_position,
        Some (ident v),
        false,
        Some (PTtyapp (qualid ["term"], [])) ))
    vars

type kind =
  | Formula
  | Term

(** Implemented cases should be kept in sync with [is_translatable] *)
let rec term_to_whyml_aux ctxt kind t =
  (* let s =
    match kind with
    | Formula -> "formula"
    | Term -> "term"
  in
  Format.printf "%a %s@." Core.Pretty.pp_term t s; *)
  match (t, kind) with
  | Unit, Term -> term (Ttuple [])
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
      tapp
        (qualid ["Int"; Ident.op_infix "*"])
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
  | Unop (Not, _), Formula -> failwith "todo not formula"
  | Unop (Not, a), Term ->
      tapp (qualid ["Bool"; "notb"]) [term_to_whyml_aux ctxt Term a]
  | Unop (Neg, _), Term -> failwith "todo unary negation"
  | Unop (Neg, _), Formula -> failwith "neg cannot be used as a formula"
  | Var x, _ ->
      (* tapp (qualid ["Var"]) [tstr (Bindlib.name_of x)] *)
      tvar (qualid [Bindlib.name_of x])
  | Symbol _, _ -> failwith "free symbol"
  | Fun _, _ -> failwith "lambdas not handled at this level"
  | Tuple _, Term -> failwith "todo tuple"
  | Tuple _, Formula -> failwith "tuple cannot be used as a formula"
  (* | Apply (Symbol { sym_name = "is_int" }, args), Formula ->
      tapp (qualid ["is_int"]) (List.map (term_to_whyml_aux ctxt Term) args) *)
  | Apply (Symbol { sym_name = f }, args), _ ->
      tapp (qualid [f]) (List.map (term_to_whyml_aux ctxt Term) args)
  | Apply (_f, _args), _ -> failwith "apply"
  | Bind (a, b), Term ->
      (* there is no let in whyml terms, only programs... *)
      (* let x, b, ctxt = Bindlib.unbind_in ctxt b in
      term
        (Tlet
           ( ident (Bindlib.name_of x),
             term_to_whyml_aux ctxt a,
             term_to_whyml_aux ctxt b )) *)
      let b1 = Bindlib.subst b a in
      term_to_whyml_aux ctxt Term b1
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
  | Binop ((Eq | Neq | Gt | Lt | Le | Ge), _, _), Formula ->
      (* ctxt  *)
      let coerce_to_prop a =
        (* let a1 = term_to_whyml_aux ctxt a in *)
        (* match a with
        | Apply (Symbol { sym_name = "is_int" }, _) -> a1
        | _ -> *)
        tapp (qualid [Ident.op_infix "="]) [a; term_to_whyml_aux ctxt Term True]
      in

      term_to_whyml_aux ctxt Term t |> coerce_to_prop
      (* failwith "Todo" *)
      (* failwith "relational operators cannot be used as a formula" *)
  | Conj (a, b), _ ->
      term
        (Tbinop
           ( term_to_whyml_aux ctxt kind a,
             Dterm.DTand,
             term_to_whyml_aux ctxt kind b ))
  | Disj (a, b), _ ->
      term
        (Tbinop
           ( term_to_whyml_aux ctxt kind a,
             Dterm.DTor,
             term_to_whyml_aux ctxt kind b ))
  | Implies (a, b), Formula ->
      (* TODO this may need to be more widely used *)
      (* let coerce_to_prop ctxt a =
        let a1 = term_to_whyml_aux ctxt a in
        match a with
        | Apply (Symbol { sym_name = "is_int" }, _) -> a1
        | _ ->
            tapp (qualid [Ident.op_infix "="]) [a1; term_to_whyml_aux ctxt True]
      in *)
      (* let a = term_to_whyml_aux ctxt a |> coerce_to_prop in *)
      (* let b = term_to_whyml_aux ctxt b |> coerce_to_prop in *)
      let a = term_to_whyml_aux ctxt Formula a in
      let b = term_to_whyml_aux ctxt Formula b in
      term (Tbinop (a, Dterm.DTimplies, b))
  | Implies _, Term -> failwith "implication cannot be used as a term"
  | Emp, _ | PointsTo _, _ | SepConj _, _ ->
      failwith "separation logic cannot be translated"
  | Subsumes _, _ -> failwith "subsumptions not handled at this level"
  | Requires _, _ | Ensures _, _ | Sequence _, _ | Shift _, _ | Reset _, _ ->
      failwith "staged logic not handled at this level"

let term_to_whyml p =
  term_to_whyml_aux Bindlib.(free_vars (box_term p)) Formula p
