open Hipcore
open Typedhip
open Utils.Hstdlib

let ident_of_binder (name, _ : binder) : string = name
let hiptypes_typ t = t

let hiptypes_bin_rel_op (t : bin_rel_op) : Hiptypes.bin_rel_op =
  match t with
  | GT -> GT
  | LT -> LT
  | EQ -> EQ
  | GTEQ -> GTEQ
  | LTEQ -> LTEQ

let hiptypes_handler_type (t : handler_type) : Hiptypes.handler_type =
  match t with Shallow -> Shallow | Deep -> Deep

let rec untype_term (t : term) : Hiptypes.term =
  match t.term_desc with
  | Const ValUnit -> Const ValUnit
  | Const (Num n) -> Const (Num n)
  | Const (TStr s) -> Const (TStr s)
  | Const TTrue -> Const TTrue
  | Const TFalse -> Const TFalse
  | Const Nil -> Const Nil
  | Var v -> Var v
  | BinOp (op, lhs, rhs) -> BinOp (op, untype_term lhs, untype_term rhs)
  | Rel (op, lhs, rhs) -> Rel (hiptypes_bin_rel_op op, untype_term lhs, untype_term rhs)
  | TNot t -> TNot (untype_term t)
  | TApp (f, args) -> TApp (f, List.map untype_term args)
  | Construct (name, args) -> Construct (name, List.map untype_term args)
  | TLambda (id, params, spec, body) ->
      TLambda (id, List.map ident_of_binder params, Option.map untype_staged_spec spec,
               Option.map untype_core_lang body)
  | TTuple ts -> TTuple (List.map untype_term ts)
and untype_pi (p : pi) : Hiptypes.pi =
  match p with
  | True -> Hiptypes.True
  | False -> Hiptypes.False
  | Atomic (op, t1, t2) -> Hiptypes.Atomic (hiptypes_bin_rel_op op, untype_term t1, untype_term t2)
  | And (p1, p2) -> Hiptypes.And (untype_pi p1, untype_pi p2)
  | Or (p1, p2) -> Hiptypes.Or (untype_pi p1, untype_pi p2)
  | Imply (p1, p2) -> Hiptypes.Imply (untype_pi p1, untype_pi p2)
  | Not p' -> Hiptypes.Not (untype_pi p')
  | Predicate (name, args) -> Hiptypes.Predicate (name, List.map untype_term args)
  | Subsumption (t1, t2) -> Hiptypes.Subsumption (untype_term t1, untype_term t2)
and untype_kappa (k : kappa) : Hiptypes.kappa =
  match k with
  | EmptyHeap -> Hiptypes.EmptyHeap
  | PointsTo (x, t) -> Hiptypes.PointsTo (x, untype_term t)
  | SepConj (k1, k2) -> Hiptypes.SepConj (untype_kappa k1, untype_kappa k2)
and untype_core_lang (c : core_lang) : Hiptypes.core_lang =
  match c.core_desc with
  | CValue v -> CValue (untype_term v)
  | CLet (x, e1, e2) -> CLet (ident_of_binder x, untype_core_lang e1, untype_core_lang e2)
  | CIfElse (cond, then_e, else_e) ->
      CIfELse (untype_pi cond, untype_core_lang then_e, untype_core_lang else_e)
  | CFunCall (fn, args) ->
      CFunCall (fn, List.map untype_term args)
  | CWrite (x, v) -> CWrite (x, untype_term v)
  | CRef v -> CRef (untype_term v)
  | CRead x -> CRead x
  | CAssert (phi, kappa) ->
      CAssert (untype_pi phi, untype_kappa kappa)
  | CPerform (eff, arg_opt) ->
      CPerform (eff, Option.map untype_term arg_opt)
  | CMatch (ht, trycatch_opt, scrutinee, handler_cases, constr_cases) ->
      let trycatch_opt' = Option.map untype_tryCatchLemma trycatch_opt in
      let handler_cases' = untype_handler_ops handler_cases in
      let constr_cases' = untype_constr_cases constr_cases in
      CMatch (hiptypes_handler_type ht, trycatch_opt', untype_core_lang scrutinee, handler_cases', constr_cases')
  | CResume vs -> CResume (List.map untype_term vs)
  | CLambda (params, spec, body) ->
      CLambda (List.map ident_of_binder params, Option.map untype_staged_spec spec, untype_core_lang body)
  | CShift (is_shift, x, body) ->
      CShift (is_shift, ident_of_binder x, untype_core_lang body)
  | CReset e -> CReset (untype_core_lang e)
  | CSequence (s1, s2) -> CSequence (untype_core_lang s1, untype_core_lang s2)
and untype_handler_ops (ops : core_handler_ops) : Hiptypes.core_handler_ops =
  List.map (fun (label, k_opt, spec, body) -> (label, k_opt, Option.map untype_staged_spec spec, untype_core_lang body)) ops
and untype_pattern (pat : pattern) : Hiptypes.pattern =
  match pat.pattern_desc with
  | PAny -> PAny
  | PVar (v, _) -> PVar v
  | PConstr (name, args) -> PConstr (name, List.map untype_pattern args)
  | PConstant c -> PConstant c
  | PAlias (p, s) -> PAlias (untype_pattern p, s)
and untype_constr_case ({ccase_pat; ccase_guard; ccase_expr} : constr_case) : Hiptypes.constr_case =
  { ccase_pat = untype_pattern ccase_pat;
    ccase_guard = Option.map untype_term ccase_guard;
    ccase_expr = untype_core_lang ccase_expr
  }
and untype_constr_cases (cases : constr_cases) : Hiptypes.constr_cases =
  List.map untype_constr_case cases
and untype_tryCatchLemma (tcl : tryCatchLemma) : Hiptypes.tryCatchLemma =
  let (head, handled_cont, summary) = tcl in
  (untype_staged_spec head, Option.map untype_staged_spec handled_cont, untype_staged_spec summary)
and untype_handlingcases (((placeholder, disj_spec), effs) : handlingcases) : Hiptypes.handlingcases =
  ((placeholder, untype_staged_spec disj_spec), List.map (fun (name, arg, disj_spec) ->
    (name, arg, untype_staged_spec disj_spec)) effs)
and untype_trycatch ((spec, cases) : trycatch) : Hiptypes.trycatch =
  (untype_staged_spec spec, untype_handlingcases cases)
and untype_instant ((eff_name, args) : instant) : Hiptypes.instant =
  (eff_name, List.map untype_term args)
and untype_staged_spec (s : staged_spec) : Hiptypes.staged_spec =
match s with
| Exists (xs, f) -> Hiptypes.Exists (ident_of_binder xs, untype_staged_spec f)
| ForAll (xs, f) -> Hiptypes.ForAll (ident_of_binder xs, untype_staged_spec f)
| Require (phi, h) ->
    Hiptypes.Require (untype_pi phi, untype_kappa h)
| NormalReturn (phi, h) ->
    Hiptypes.NormalReturn (untype_pi phi, untype_kappa h)
| HigherOrder (f, t) ->
    Hiptypes.HigherOrder (f, List.map untype_term t)
| Shift (is_shift, k, spec, x, cont) ->
    Hiptypes.Shift (is_shift, ident_of_binder k, untype_staged_spec spec, ident_of_binder x, untype_staged_spec cont)
| Disjunction (f1, f2) ->
    Hiptypes.Disjunction (untype_staged_spec f1, untype_staged_spec f2)
| Sequence (f1, f2) ->
    Hiptypes.Sequence (untype_staged_spec f1, untype_staged_spec f2)
| Bind (x, f1, f2) ->
    Hiptypes.Bind (ident_of_binder x, untype_staged_spec f1, untype_staged_spec f2)
| Reset (spec, cont) ->
    Hiptypes.Reset (untype_staged_spec spec, untype_term cont)
| RaisingEff (phi, h, inst, t) ->
    Hiptypes.RaisingEff (untype_pi phi, untype_kappa h, untype_instant inst, untype_term t)
| TryCatch (phi, h, tc, t) ->
    Hiptypes.TryCatch (untype_pi phi, untype_kappa h, untype_trycatch tc, untype_term t)

let untype_state ((p, k) : state) : Hiptypes.state  =
  (untype_pi p, untype_kappa k)

let untype_single_subsumption_obligation (vars, (l, r)) =
  (vars, (untype_staged_spec l, untype_staged_spec r))

let untype_subsumption_obligation ls =
  List.map untype_single_subsumption_obligation ls

let untype_bindings (bindings : (binder * term) list) : (string * Hiptypes.term) list =
  List.map (fun (b, t) -> (ident_of_binder b, untype_term t)) bindings

let untype_lemma Typedhip.{ l_name; l_params; l_left; l_right } =
  Hiptypes.{ l_name;
    l_params = List.map ident_of_binder l_params;
    l_left = untype_staged_spec l_left;
    l_right = untype_staged_spec l_right;
  }

let untype_pure_fn_def Typedhip.{ pf_name; pf_params; pf_ret_type; pf_body } : Hiptypes.pure_fn_def =
  { pf_name;
    pf_params = List.map ident_of_binder pf_params;
    pf_ret_type;
    pf_body = untype_core_lang pf_body; }

let untype_meth_def Typedhip.{ m_name; m_params; m_spec; m_body; m_tactics } : Hiptypes.meth_def =
  { m_name;
    m_params = List.map ident_of_binder m_params;
    m_spec = Option.map untype_staged_spec m_spec;
    m_body = untype_core_lang m_body;
    m_tactics }

let untype_pred_def Typedhip.{p_name; p_params; p_body; p_rec} : Hiptypes.pred_def =
  { p_name;
    p_params = List.map ident_of_binder p_params;
    p_body = untype_staged_spec p_body;
    p_rec }

let untype_sl_pred_def Typedhip.{p_sl_ex; p_sl_name; p_sl_params; p_sl_body} : Hiptypes.sl_pred_def =
  { p_sl_ex = List.map ident_of_binder p_sl_ex;
    p_sl_name;
    p_sl_params = List.map ident_of_binder p_sl_params;
    p_sl_body = untype_state p_sl_body }

let untype_core_program Typedhip.{ cp_effs; cp_predicates; cp_sl_predicates; cp_lemmas; cp_methods } : Hiptypes.core_program =
  { cp_effs;
    cp_predicates = SMap.map untype_pred_def cp_predicates;
    cp_sl_predicates = SMap.map untype_sl_pred_def cp_sl_predicates;
    cp_lemmas = SMap.map untype_lemma cp_lemmas;
    cp_methods = List.map untype_meth_def cp_methods }
