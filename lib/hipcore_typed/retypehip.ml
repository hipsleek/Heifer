(** Module for transforming a Hiptypes AST element into a Typedhip element.
    All types are filled in with placeholders, to be populated during typechecking. Since
    there are utilities that take the Typedtree as input, most program types should be coming from
    the OCaml typechecker; this is used to typecheck annotations.*)

open Hipcore
open Typedhip

let binder_of_ident ?(typ=Types.new_type_var ()) (ident : string) : binder = (ident, typ)

let rec retype_term (term : Hiptypes.term) =
  let term_desc = match term with
  | Hiptypes.Const (ValUnit) -> Const ValUnit
  | Hiptypes.Const (Num n) -> Const (Num n)
  | Hiptypes.Var v -> Var v
  | Hiptypes.Const (TStr s) -> Const (TStr s)
  | Hiptypes.BinOp (op, lhs, rhs) -> BinOp (op, retype_term lhs, retype_term rhs)
  | Hiptypes.Rel (op, lhs, rhs) -> Rel (op, retype_term lhs, retype_term rhs)
  | Hiptypes.Const TTrue -> Const TTrue
  | Hiptypes.Const TFalse -> Const TFalse
  | Hiptypes.TNot t -> TNot (retype_term t)
  | Hiptypes.TApp (f, args) -> TApp (f, List.map retype_term args)
  | Hiptypes.Const Nil -> Const Nil
  | Hiptypes.TLambda (id, params, spec, body) ->
      TLambda (id, List.map binder_of_ident params,
               Option.map retype_staged_spec spec,
               Option.map retype_core_lang body)
  | Hiptypes.Construct (name, args) -> Construct (name, List.map retype_term args)
  | Hiptypes.TTuple ts -> TTuple (List.map retype_term ts)
  in
  { term_desc; term_type = Types.new_type_var () }
and retype_pi (pi : Hiptypes.pi) =
  match pi with
  | Hiptypes.True -> True
  | Hiptypes.False -> False
  | Hiptypes.Atomic (op, lhs, rhs) -> Atomic (op, retype_term lhs, retype_term rhs)
  | Hiptypes.And (lhs, rhs) -> And (retype_pi lhs, retype_pi rhs)
  | Hiptypes.Or (lhs, rhs) -> Or (retype_pi lhs, retype_pi rhs)
  | Hiptypes.Imply (lhs, rhs) -> Imply (retype_pi lhs, retype_pi rhs)
  | Hiptypes.Not p -> Not (retype_pi p)
  | Hiptypes.Predicate (name, args) -> Predicate (name, List.map retype_term args)
  | Hiptypes.Subsumption (lhs, rhs) -> Subsumption (retype_term lhs, retype_term rhs)
and retype_kappa (kappa : Hiptypes.kappa) =
  match kappa with
  | Hiptypes.EmptyHeap -> EmptyHeap
  | Hiptypes.PointsTo (loc, value) -> PointsTo (loc, retype_term value)
  | Hiptypes.SepConj (k1, k2) -> SepConj (retype_kappa k1, retype_kappa k2)
and retype_instant ((name, args) : Hiptypes.instant) = (name, List.map retype_term args)
and retype_handlingcases (((default_var, default_spec), effects) : Hiptypes.handlingcases) : handlingcases =
  ((default_var, retype_staged_spec default_spec), effects |> List.map (fun (eff, args, spec) -> (eff, args, retype_staged_spec spec)))
and retype_trycatch ((spec, cases) : Hiptypes.trycatch) : trycatch =
  (retype_staged_spec spec, retype_handlingcases cases)
and retype_staged_spec (staged_spec : Hiptypes.staged_spec) : staged_spec =
  match staged_spec with
  | Hiptypes.Exists (var, spec) -> Exists (binder_of_ident var, retype_staged_spec spec)
  | Hiptypes.ForAll (var, spec) -> ForAll (binder_of_ident var, retype_staged_spec spec)
  | Hiptypes.Bind (v, s1, s2) -> Bind (binder_of_ident v, retype_staged_spec s1, retype_staged_spec s2)
  | Hiptypes.Sequence (s1, s2) -> Sequence (retype_staged_spec s1, retype_staged_spec s2)
  | Hiptypes.Disjunction (s1, s2) -> Disjunction (retype_staged_spec s1, retype_staged_spec s2)
  | Hiptypes.Require (p, k) -> Require (retype_pi p, retype_kappa k)
  | Hiptypes.NormalReturn (p, k) -> NormalReturn (retype_pi p, retype_kappa k)
  | Hiptypes.HigherOrder (name, args) -> HigherOrder (name, List.map retype_term args)
  | Hiptypes.Shift (b, k, body, x, cont) -> Shift (b, binder_of_ident k, retype_staged_spec body, binder_of_ident x, retype_staged_spec cont)
  | Hiptypes.Reset (s, x, cont) -> Reset (retype_staged_spec s, binder_of_ident x, retype_staged_spec cont)
  | Hiptypes.RaisingEff (p, k, ins, t) -> RaisingEff (retype_pi p, retype_kappa k, retype_instant ins, retype_term t)
  | Hiptypes.TryCatch (p, k, trycatch, t) -> TryCatch (retype_pi p, retype_kappa k, retype_trycatch trycatch, retype_term t)
and retype_constr_case ({ccase_pat; ccase_guard; ccase_expr} : Hiptypes.constr_case) : constr_case =
  { ccase_pat = retype_pattern ccase_pat;
    ccase_guard = Option.map retype_term ccase_guard;
    ccase_expr = retype_core_lang ccase_expr
  }
and retype_constr_cases (cases : Hiptypes.constr_cases) : constr_cases =
  List.map retype_constr_case cases
and retype_pattern (pat : Hiptypes.pattern) : pattern =
  let pattern_desc = match pat with
  | PAny -> PAny
  | PVar var -> PVar (binder_of_ident var)
  | PConstr (name, args) -> PConstr (name, List.map retype_pattern args)
  | PConstant c -> PConstant c
  | PAlias (p, v) -> PAlias (retype_pattern p, v)
  in
  {pattern_desc; pattern_type = Types.new_type_var ()}
and retype_try_catch_lemma ((spec, cont, summary) : Hiptypes.tryCatchLemma) : tryCatchLemma =
  (retype_staged_spec spec, Option.map retype_staged_spec cont, retype_staged_spec summary)
and retype_core_handler_ops (handlers : Hiptypes.core_handler_ops) : core_handler_ops =
  List.map (fun (name, cont, spec, expr) -> (name, cont, Option.map retype_staged_spec spec, retype_core_lang expr)) handlers
and retype_core_lang (core_lang : Hiptypes.core_lang) : core_lang =
  let core_desc = match core_lang with
  | Hiptypes.CValue cvalue -> CValue (retype_term cvalue)
  | Hiptypes.CLet (var, value, expr) -> CLet (binder_of_ident var, retype_core_lang value, retype_core_lang expr)
  | Hiptypes.CIfELse (cond, then_, else_) -> CIfElse (retype_pi cond, retype_core_lang then_, retype_core_lang else_)
  | Hiptypes.CFunCall (name, args) -> CFunCall (name, List.map retype_term args)
  | Hiptypes.CWrite (loc, value) -> CWrite (loc, retype_term value)
  | Hiptypes.CRef value -> CRef (retype_term value)
  | Hiptypes.CRead loc -> CRead loc
  | Hiptypes.CAssert (p, k) -> CAssert (retype_pi p, retype_kappa k)
  | Hiptypes.CPerform (eff, args) -> CPerform (eff, Option.map retype_term args)
  | Hiptypes.CMatch (handler_type, lemma, scrutinee, computation_cases, value_cases) ->
      CMatch (handler_type, Option.map retype_try_catch_lemma lemma, retype_core_lang scrutinee,
      retype_core_handler_ops computation_cases, retype_constr_cases value_cases)
  | Hiptypes.CResume args -> CResume (List.map retype_term args)
  | Hiptypes.CLambda (args, spec, body) -> CLambda (List.map binder_of_ident args, Option.map retype_staged_spec spec, retype_core_lang body)
  | Hiptypes.CShift _ | Hiptypes.CReset _ -> failwith "TODO"
  | Hiptypes.CSequence (s1, s2) -> CSequence (retype_core_lang s1, retype_core_lang s2)
  in
  {core_desc; core_type = Types.new_type_var ()}
let retype_state ((pi, kappa) : Hiptypes.state) : state = (retype_pi pi, retype_kappa kappa)
let retype_pred_def (d : Hiptypes.pred_def) : pred_def =
  { p_name = Hiptypes.(d.p_name);
    p_params = List.map binder_of_ident Hiptypes.(d.p_params);
    p_body = retype_staged_spec Hiptypes.(d.p_body);
    p_rec = Hiptypes.(d.p_rec);
  }

let retype_lambda_obligation (lo : Hiptypes.lambda_obligation) : lambda_obligation =
  { lo_name = Hiptypes.(lo.lo_name);
    lo_preds = Common.SMap.map retype_pred_def Hiptypes.(lo.lo_preds);
    lo_left = retype_staged_spec Hiptypes.(lo.lo_left);
    lo_right = retype_staged_spec Hiptypes.(lo.lo_right);
  }

let retype_meth_def (d : Hiptypes.meth_def) : meth_def =
  { m_name = Hiptypes.(d.m_name);
    m_params = List.map binder_of_ident d.m_params;
    m_spec = Option.map retype_staged_spec Hiptypes.(d.m_spec);
    m_body = retype_core_lang Hiptypes.(d.m_body);
    m_tactics = Hiptypes.(d.m_tactics)
  }
let retype_sl_pred_def (d : Hiptypes.sl_pred_def) : sl_pred_def =
  { p_sl_ex = List.map binder_of_ident d.p_sl_ex;
    p_sl_name = d.p_sl_name;
    p_sl_params = List.map binder_of_ident d.p_sl_params;
    p_sl_body = retype_state d.p_sl_body
  }

let retype_single_subsumption_obligation (vars, (l, r)) =
  (vars, (retype_staged_spec l, retype_staged_spec r))

let retype_subsumption_obligation ls =
  List.map retype_single_subsumption_obligation ls


let retype_lemma (l : Hiptypes.lemma) : lemma =
{ l_name = l.l_name;
  l_params = List.map binder_of_ident l.l_params;
  l_left = retype_staged_spec l.l_left;
  l_right = retype_staged_spec l.l_right
}

let retype_intermediate (i : Hiptypes.intermediate) : intermediate =
  match i with
  | Eff name -> Eff name
  | Lem lemma -> Lem (retype_lemma lemma)
  | LogicTypeDecl (name, typs, ret_typ, path, lname) ->
      LogicTypeDecl (name, typs, ret_typ, path, lname)
  | Meth (name, params, spec, body, tactics, pure_fn_info) ->
      Meth (name, List.map binder_of_ident params, Option.map retype_staged_spec spec, retype_core_lang body,
      tactics, Option.map (fun (typs, ret) -> (typs, ret)) pure_fn_info)
  | Pred pred_def -> Pred (retype_pred_def pred_def)
  | SLPred sl_pred_def -> SLPred (retype_sl_pred_def sl_pred_def)
  | Typedef t -> Typedef t

let retype_bindings (bindings : (string * Hiptypes.term) list) : (binder * term) list =
  List.map (fun (b, t) -> (binder_of_ident b, retype_term t)) bindings
