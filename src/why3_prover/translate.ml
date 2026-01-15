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
  | Binop ((Lt | Le | Gt | Ge | Eq | Neq | Plus | Times | Cons), _, _)
  | Unop ((Not | Neg), _) ->
      (* terms *)
      true
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

(** Implemented cases should be kept in sync with [is_translatable] *)
let rec term_to_whyml_aux ctxt t =
  match t with
  | Unit -> term (Ttuple [])
  | True -> tapp (qualid ["TBool"]) [term Ttrue]
  | False -> tapp (qualid ["TBool"]) [term Tfalse]
  | Nil ->
      (* tapp (qualid ["TNil"]) []  *)
      tvar (qualid ["TNil"])
  | Int i -> tapp (qualid ["TInt"]) [tconst i]
  | Binop (Times, a, b) ->
      tapp
        (qualid ["Int"; Ident.op_infix "*"])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Plus, a, b) ->
      (* tapp (qualid ["Int"; Ident.op_infix "+"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b] *)
      tapp (qualid ["plus"])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Cons, h, t) ->
      tapp (qualid ["TCons"])
        [term_to_whyml_aux ctxt h; term_to_whyml_aux ctxt t]
  | Unop (Not, a) -> tapp (qualid ["Bool"; "notb"]) [term_to_whyml_aux ctxt a]
  | Unop (Neg, _) -> failwith "todo unary negation"
  | Var x ->
      (* tapp (qualid ["Var"]) [tstr (Bindlib.name_of x)] *)
      tvar (qualid [Bindlib.name_of x])
  | Symbol _ -> failwith "free symbol"
  | Fun _ -> failwith "todo fun"
  | Tuple _ -> failwith "todo tuple"
  | Apply (Symbol { sym_name = f }, args) ->
      tapp (qualid [f]) (List.map (term_to_whyml_aux ctxt) args)
  | Apply (_f, _args) -> failwith "apply"
  | Bind (a, b) ->
      (* there is no let in whyml terms, only programs... *)
      (* let x, b, ctxt = Bindlib.unbind_in ctxt b in
      term
        (Tlet
           ( ident (Bindlib.name_of x),
             term_to_whyml_aux ctxt a,
             term_to_whyml_aux ctxt b )) *)
      let b1 = Bindlib.subst b a in
      term_to_whyml_aux ctxt b1
  | Forall b ->
      let xs, b, ctxt = Bindlib.unmbind_in ctxt b in
      let xs = Array.to_list xs |> List.map Bindlib.name_of in
      term
        (Tquant (Dterm.DTforall, vars_to_params xs, [], term_to_whyml_aux ctxt b))
  | Exists b ->
      let xs, b, ctxt = Bindlib.unmbind_in ctxt b in
      let xs = Array.to_list xs |> List.map Bindlib.name_of in
      term
        (Tquant (Dterm.DTexists, vars_to_params xs, [], term_to_whyml_aux ctxt b))
  | Binop (Eq, a, b) ->
      tapp
        (qualid [Ident.op_infix "="])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Gt, a, b) ->
      tapp (qualid ["gt"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Lt, a, b) ->
      tapp (qualid ["lt"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Le, a, b) ->
      tapp (qualid ["le"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Ge, a, b) ->
      tapp (qualid ["ge"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Neq, a, b) ->
      tapp (qualid ["neq"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Conj (a, b) ->
      term
        (Tbinop (term_to_whyml_aux ctxt a, Dterm.DTand, term_to_whyml_aux ctxt b))
  | Disj (a, b) ->
      term
        (Tbinop (term_to_whyml_aux ctxt a, Dterm.DTor, term_to_whyml_aux ctxt b))
  | Implies (a, b) ->
      term
        (Tbinop
           (term_to_whyml_aux ctxt a, Dterm.DTimplies, term_to_whyml_aux ctxt b))
  | Emp | PointsTo _ | SepConj _ ->
      failwith "separation logic cannot be translated"
  | Subsumes _ -> failwith "subsumptions not handled at this level"
  | Requires _ | Ensures _ | Sequence (_, _) | Shift _ | Reset _ ->
      failwith "staged logic not handled at this level"

let term_to_whyml p = term_to_whyml_aux Bindlib.(free_vars (box_term p)) p
