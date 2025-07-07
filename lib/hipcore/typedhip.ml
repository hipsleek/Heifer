
open Types
[@@@warning "-17"]
(* can also appear in pi *)
type bin_rel_op = Hiptypes.bin_rel_op =  GT | LT | EQ | GTEQ | LTEQ
and binder = string * typ
and bin_term_op = Hiptypes.bin_term_op = Plus | Minus | SConcat | TAnd | TPower | TTimes | TDiv | TOr | TCons
and const = Hiptypes.const =
  | ValUnit
  | Num of int
  | TStr of string
  | Nil
  | TTrue
  | TFalse
and term_desc =
  | Const of const
  | Var of string
  | Rel of bin_rel_op * term * term
  | BinOp of bin_term_op * term * term
  | TNot of term
  | TApp of string * term list
  (* constructor of an inductive datatype *)
  | Construct of string * term list
  (* the string is just an identifier for uniqueness.
     the last param is the name of the result *)
  (* The string seems to be redundant here and I think we should remove it if possible *)
  | TLambda of string * binder list * staged_spec option * core_lang option
  (* unused *)
  | TTuple of term list
and term =
  {
    term_desc: term_desc;
    term_type: typ
  }

(* (Label n) _k (*@ spec @*) -> e *)
and core_handler_ops = (string * string option * staged_spec option * core_lang) list
(* x :: xs -> e is represented as ("::", [x, xs], e) *)
(* effect work; let's group them into a single blob *)
and constr_case = {
  ccase_pat : pattern;
  ccase_guard : term option;
  ccase_expr : core_lang
}
and constr_cases = constr_case list

and pattern_desc =
  | PVar of binder
  | PConstr of (string * pattern list)
  | PConstant of const
  | PAlias of pattern * string
  | PAny

and pattern =
  {
    pattern_desc: pattern_desc;
    pattern_type: typ
  }
and tryCatchLemma = (staged_spec * staged_spec option * (*(handlingcases) **) staged_spec) (*tcl_head, tcl_handledCont, tcl_summary*)
and handler_type = Hiptypes.handler_type = Shallow | Deep

and core_value = term
and core_lang_desc =
  | CValue of core_value
  | CLet of binder * core_lang * core_lang
  | CSequence of core_lang * core_lang
  | CIfElse of (*core_value*) pi * core_lang * core_lang
  | CFunCall of string * (core_value) list
  | CWrite of string * core_value
  | CRef of core_value
  | CRead of string
  | CAssert of pi * kappa
  (* effect start *)
  | CPerform of string * core_value option
  (* match e with | eff case... | constr case... *)
  | CMatch of handler_type * tryCatchLemma option * core_lang * core_handler_ops * constr_cases
  | CResume of core_value list
  (* effect end *)
  | CLambda of binder list * staged_spec option * core_lang
  | CShift of bool * binder * core_lang (* bool=true is for shift, and bool=false for shift0 *)
  | CReset of core_lang

and core_lang =
  {core_desc: core_lang_desc;
   core_type: typ}
(* an occurrence of an effect *)
and instant = string * term list
and pi =
  | True
  | False
  | Atomic of bin_rel_op * term * term
  | And    of pi * pi
  | Or     of pi * pi
  | Imply  of pi * pi
  | Not    of pi
  | Predicate of string * term list
  | Subsumption of term * term

and kappa =
  | EmptyHeap
  (* x -> -   means x is allocated, and - is encoded as Var "_" *)
  (* TODO should PointsTo use binders instead of strings...? *)
  | PointsTo of (string * term)
  | SepConj of kappa * kappa
  (*| MagicWand of kappa * kappa*)

(* a formula which describes a program state *)
and state = pi * kappa

(* effect start *)
(* v->phi and (Eff arg?-> phi)* *)
and handlingcases = (string * staged_spec) * ((string * string option * staged_spec) list)
and trycatch = (staged_spec * handlingcases)
(* effect end *)

and staged_spec =
  | Exists of binder * staged_spec
  | ForAll of binder * staged_spec
  | Require of pi * kappa
  (* ens H /\ P, where P may contain contraints on res *)
  (* | Ens_Pure of pi
  | Ens_Heap of kappa
  | Ens_Result of term *)
  | NormalReturn of pi * kappa
  (* higher-order functions: H /\ P /\ f$(...args, term) *)
  (* this constructor is also used for inductive predicate applications *)
  (* f$(x, y) is HigherOrder(..., ..., (f, [x]), y) *)
  | HigherOrder of string * term list
  | Shift of bool * string * staged_spec (* see CShift for meaning of bool *)
  | Reset of staged_spec
  | Sequence of staged_spec * staged_spec
  | Bind of string * staged_spec * staged_spec
  | Disjunction of staged_spec * staged_spec
  (* effects: H /\ P /\ E(...args, v), term is always a placeholder variable *)
  | RaisingEff of (pi * kappa * instant * term)
  (* | IndPred of { name : string; args: term list } *)
  | TryCatch of (pi * kappa * trycatch * term)
(* copied here so visitors can be generated *)
and typ = Types.typ = 
  | Any
  | Unit
  | TConstr of string * typ list
  | Int
  | Bool
  | TyString
  | Lamb
  | Arrow of typ * typ
  | TVar of string

[@@deriving
  visitors { variety = "map"; name = "map_spec" },
  visitors { variety = "reduce"; name = "reduce_spec" },
  ord]

let var_of_binder (v, t) = {term_desc = Var v; term_type = t}

type tactic = Hiptypes.tactic

type meth_def = {
  m_name : string;
  m_params : binder list;
  m_spec : staged_spec option;
  m_body : core_lang;
  m_tactics : tactic list;
}

type sl_pred_def = {
  p_sl_ex: binder list;
  p_sl_name: string;
  p_sl_params: binder list; (* list to ensure ordering. last param is typically a return value *)
  p_sl_body: pi * kappa;
}

type pred_def = {
  p_name: string;
  p_params: binder list; (* list to ensure ordering. last param is typically a return value *)
  p_body: staged_spec;
  p_rec: bool;
}

type lemma = {
  l_name: string;
  l_params: binder list; (* ordered, the last parameter is a result *)
  l_left: staged_spec;
  l_right: staged_spec; (* could also be disj_spec but not needed *)
}

type lambda_obligation = {
  lo_name: string;
  lo_preds: pred_def Common.SMap.t;
  lo_left: staged_spec;
  lo_right: staged_spec;
}

(** A pure function that can be imported directly into SMT *)
type pure_fn_def = {
  pf_name: string;
  pf_params: binder list;
  pf_ret_type: typ;
  pf_body: core_lang;
}

type pure_fn_type_def = {
  pft_name: string;
  pft_logic_path: string list;
  pft_logic_name: string;
  pft_params: typ list;
  pft_ret_type: typ;
}

type intermediate =
  | Eff of string
  | Lem of lemma
  | LogicTypeDecl of string * typ list * typ * string list * string
  (* name, params, spec, body, tactics, pure_fn_info *)
  | Meth of string * binder list * staged_spec option * core_lang * tactic list * (typ list * typ) option
  (* user-provided type definition *)
  | Typedef of type_declaration
  | Pred of pred_def
  | SLPred of sl_pred_def

type core_program = {
  cp_effs: string list;
  cp_predicates: pred_def Common.SMap.t;
  cp_sl_predicates: sl_pred_def Common.SMap.t;
  cp_lemmas: lemma Common.SMap.t;
  cp_methods: meth_def list;
}

let empty_program = {
  cp_effs = [];
  cp_methods = [];
  cp_predicates = Common.SMap.empty;
  cp_sl_predicates = Common.SMap.empty;
  cp_lemmas = Common.SMap.empty
}

type 'a quantified = binder list * 'a
