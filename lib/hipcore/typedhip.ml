
[@@@warning "-17"]
(* can also appear in pi *)
type bin_rel_op = [%import: Hiptypes.bin_rel_op]
and binder = string * typ option
and bin_term_op = Plus | Minus | SConcat | TAnd | TPower | TTimes | TDiv | TOr | TCons
and const =
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
  (* the string is just an identifier for uniqueness.
     the last param is the name of the result *)
  (* The string seems to be redundant here and I think we should remove it if possible *)
  | TLambda of string * binder list * staged_spec option * core_lang option
  (* unused *)
  | TList of term list
  | TTuple of term list
and term =
  {
    term_desc: term_desc;
    term_type: typ option
  }

(* (Label n) _k (*@ spec @*) -> e *)
and core_handler_ops = (string * string option * staged_spec option * core_lang) list
(* x :: xs -> e is represented as ("::", [x, xs], e) *)
(* effect work; let's group them into a single blob *)
and constr_cases = (string * binder list * core_lang) list
and tryCatchLemma = (staged_spec * staged_spec option * (*(handlingcases) **) staged_spec) (*tcl_head, tcl_handledCont, tcl_summary*)
and handler_type = [%import : Hiptypes.handler_type]

and core_value = term
and core_lang_desc =
  | CValue of core_value
  | CLet of binder * core_lang * core_lang
  | CIfElse of (*core_value*) pi * core_lang * core_lang
  | CFunCall of string * (core_value) list
  | CWrite of string * core_value
  | CRef of core_value
  | CRead of string
  | CAssert of pi * kappa
  (* effect start *)
  | CPerform of string * core_value option
  (* match e with | v -> e1 | eff case... | constr case... *)
  | CMatch of handler_type * tryCatchLemma option * core_lang * (binder * core_lang) option * core_handler_ops * constr_cases
  | CResume of core_value list
  (* effect end *)
  | CLambda of binder list * staged_spec option * core_lang
  | CShift of bool * binder * core_lang (* bool=true is for shift, and bool=false for shift0 *)
  | CReset of core_lang

and core_lang =
  {core_desc: core_lang_desc;
   core_type: typ option}
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
  | Exists of string * staged_spec
  | Require of pi * kappa
  (* ens H /\ P, where P may contain contraints on res *)
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

(* and spec = stagedSpec list *)
(* and disj_spec = spec list *)

and typ = [%import : Hiptypes.typ]

[@@deriving
  visitors { variety = "map"; name = "map_spec" },
  visitors { variety = "reduce"; name = "reduce_spec" },
  ord]
(*
let min_typ a b = if compare_typ a b <= 0 then a else b
let is_concrete_type = function TVar _ -> false | _ -> true
let res_eq t = Atomic (EQ, {term_desc = Var "res"; term_type = t.term_type}, t)

module TMap = Map.Make (struct
  type t = typ
  let compare = compare_typ
end)

module U = Hiptypes.U

module TEnv = Hiptypes.TEnv

type abs_typ_env = Hiptypes.abs_typ_env
let create_abs_env = Hiptypes.create_abs_env

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
  l_left: instant; (* for simplicity of rewriting *)
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

type normalStage =  (binder list* (pi * kappa ) * (pi * kappa))
[@@deriving
  visitors { variety = "map"; name = "map_normal_stages_" },
  visitors { variety = "reduce"; name = "reduce_normal_stages_" }]

type shiftStage = {
  s_evars : binder list;
  s_notzero : bool;
  s_pre : pi * kappa;
  s_post : pi * kappa;
  s_cont : binder;
  s_body : disj_spec;
  s_ret : term;
}
[@@deriving
  visitors { variety = "map"; name = "map_shift_stage_" },
  visitors { variety = "reduce"; name = "reduce_shift_stage_" }]

type resetStage = {
  rs_evars : binder list;
  rs_pre : pi * kappa;
  rs_post : pi * kappa;
  rs_body : disj_spec;
  rs_ret : term;
}
[@@deriving
  visitors { variety = "map"; name = "map_reset_stage_" },
  visitors { variety = "reduce"; name = "reduce_reset_stage_" }]

type tryCatchStage = {
  tc_evars : binder list;
  tc_pre : pi * kappa;
  tc_post : pi * kappa;
  tc_constr : trycatch;
  tc_ret : term;
}
[@@deriving
  visitors { variety = "map"; name = "map_try_catch_stage_" },
  visitors { variety = "reduce"; name = "reduce_try_catch_stage_" }]
type effectStage = {
  e_evars : binder list;
  e_pre : pi * kappa;
  e_post : pi * kappa;
  e_constr : instant;
  e_ret : term;
  e_typ : [`Eff | `Fn] [@opaque];
}
[@@deriving
  visitors { variety = "map"; name = "map_effect_stage_" },
  visitors { variety = "reduce"; name = "reduce_effect_stage_" }]

type effHOTryCatchStages =
  | EffHOStage of effectStage
  | ShiftStage of shiftStage
  | TryCatchStage of tryCatchStage
  | ResetStage of resetStage

[@@deriving
  visitors { variety = "map"; name = "map_eff_stages_" },
  visitors { variety = "reduce"; name = "reduce_eff_stages_" }]
type normalisedStagedSpec = effHOTryCatchStages list * normalStage
[@@deriving
  visitors { variety = "map"; name = "map_normalised_" },
  visitors { variety = "reduce"; name = "reduce_normalised_" }]

class virtual ['self] map_normalised =
  object (_ : 'self)
    inherit [_] map_spec
    inherit! [_] map_effect_stage_
    inherit! [_] map_shift_stage_
    inherit! [_] map_try_catch_stage_
    inherit! [_] map_reset_stage_
    inherit! [_] map_eff_stages_
    inherit! [_] map_normal_stages_
    inherit! [_] map_normalised_
  end

class virtual ['self] reduce_normalised =
  object (_ : 'self)
    inherit [_] reduce_spec
    inherit! [_] reduce_effect_stage_
    inherit! [_] reduce_shift_stage_
    inherit! [_] reduce_try_catch_stage_
    inherit! [_] reduce_reset_stage_
    inherit! [_] reduce_eff_stages_
    inherit! [_] reduce_normal_stages_
    inherit! [_] reduce_normalised_
  end
*)

let new_type_var : ?name:string -> unit -> typ =
  (* let counter = ref 0 in begin *)
  (* fun ?(name="") () -> *)
  (*   counter := !counter + 1; *)
  (*   TVar (if name = "" then "[tvar " ^ string_of_int !counter ^ "]" else name) *)
  (* end *)
  (* FIXME temp fix to make anonymous/filled types irrelevant for equality checking *)
  fun ?(name="_") _ -> TVar name

(* let binder_of_ident ?(typ=new_type_var ()) (ident : string) : binder =
  (ident, typ) *)

let ident_of_binder ((name, _) : binder) = name

let var_from_binder ((name, typ) : binder) = {term_desc = Var name; term_type = typ}

let binder_of_var (var : term) =
  match var with
  | {term_desc = Var name; term_type} -> (name, term_type)
  | _ -> raise (Invalid_argument "binder_of_var: Not a variable")

(* Modules regarding converting a Typedhip AST to a Hiptypes AST and vice versa.
   There may be interest in using an Untypeast-like API for this instead, to allow
   for extensibility. *)

(* module Fill_type = struct
  (** Module for transforming a Hiptypes AST element into a Typedhip element.
      All types are filled in with placeholders, to be populated during typechecking. Since
      there are utilities that take the Typedtree as input, most program types should be coming from
      the OCaml typechecker; this is used to typecheck annotations.*)


  let from_hiptypes_typ : Hiptypes.typ -> typ = Fun.id
    (* | List_int -> TConstr ("list", [Int]) *)
    (* | TConstr (name, args) -> TConstr (name, args) *)
    (* | TyUnit -> TyUnit *)
    (* | Int -> Int *)
    (* | Bool -> Bool *)
    (* | TyString -> TyString *)
    (* | Lamb -> Lamb *)
    (* | TVar s -> TVar s *)
    (* | Arrow (x, y) -> Arrow (from_hiptypes_typ x, from_hiptypes_typ y) *)

  let rec fill_untyped_term (term : Hiptypes.term) =
    let term_desc = match term with
    | Hiptypes.UNIT -> Const ValUnit
    | Hiptypes.Num n -> Const (Num n)
    | Hiptypes.Var v -> Var v
    | Hiptypes.TStr s -> Const (TStr s)
    | Hiptypes.Plus (lhs, rhs) -> BinOp (Plus, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.Minus (lhs, rhs) -> BinOp (Minus, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.SConcat (lhs, rhs) -> BinOp (SConcat, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.Rel (op, lhs, rhs) -> Rel (op, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TTrue -> Const TTrue
    | Hiptypes.TFalse -> Const TFalse
    | Hiptypes.TAnd (lhs, rhs) -> BinOp (TAnd, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TPower (lhs, rhs) -> BinOp (TPower, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TTimes (lhs, rhs) -> BinOp (TTimes, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TDiv (lhs, rhs) -> BinOp (TDiv, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TOr (lhs, rhs) -> BinOp (TOr, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TNot t -> TNot (fill_untyped_term t)
    | Hiptypes.TApp (f, args) -> TApp (f, List.map fill_untyped_term args)
    | Hiptypes.TCons (lhs, rhs) -> BinOp (TCons, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.Nil -> Const Nil
    | Hiptypes.TLambda (id, params, spec, body) ->
        TLambda (id, List.map binder_of_ident params,
                 fill_untyped_disj_spec spec,
                 Option.map fill_untyped_core_lang body)
    | Hiptypes.TList ts -> TList (List.map fill_untyped_term ts)
    | Hiptypes.TTupple ts -> TTuple (List.map fill_untyped_term ts)
    in
    { term_desc; term_type = new_type_var () }
  and fill_untyped_pi (pi : Hiptypes.pi) =
    match pi with
    | Hiptypes.True -> True
    | Hiptypes.False -> False
    | Hiptypes.Atomic (op, lhs, rhs) -> Atomic (op, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.And (lhs, rhs) -> And (fill_untyped_pi lhs, fill_untyped_pi rhs)
    | Hiptypes.Or (lhs, rhs) -> Or (fill_untyped_pi lhs, fill_untyped_pi rhs)
    | Hiptypes.Imply (lhs, rhs) -> Imply (fill_untyped_pi lhs, fill_untyped_pi rhs)
    | Hiptypes.Not p -> Not (fill_untyped_pi p)
    | Hiptypes.Predicate (name, args) -> Predicate (name, List.map fill_untyped_term args)
    | Hiptypes.Subsumption (lhs, rhs) -> Subsumption (fill_untyped_term lhs, fill_untyped_term rhs)
  and fill_untyped_kappa (kappa : Hiptypes.kappa) =
    match kappa with
    | Hiptypes.EmptyHeap -> EmptyHeap
    | Hiptypes.PointsTo (loc, value) -> PointsTo (loc, fill_untyped_term value)
    | Hiptypes.SepConj (k1, k2) -> SepConj (fill_untyped_kappa k1, fill_untyped_kappa k2)
  and fill_untyped_instant ((name, args) : Hiptypes.instant) = (name, List.map fill_untyped_term args)
  and fill_untyped_handlingcases (((default_var, default_spec), effects) : Hiptypes.handlingcases) : handlingcases =
    ((default_var, fill_untyped_disj_spec default_spec), effects |> List.map (fun (eff, args, spec) -> (eff, args, fill_untyped_disj_spec spec)))
  and fill_untyped_trycatch ((spec, cases) : Hiptypes.trycatch) : trycatch =
    (fill_untyped_spec spec, fill_untyped_handlingcases cases)
  and fill_untyped_spec_stage (spec : Hiptypes.stagedSpec) =
    match spec with
    | Hiptypes.Exists vars -> Exists (List.map binder_of_ident vars)
    | Hiptypes.Require (p, k) -> Require (fill_untyped_pi p, fill_untyped_kappa k)
    | Hiptypes.NormalReturn (p, k) -> NormalReturn (fill_untyped_pi p, fill_untyped_kappa k)
    | Hiptypes.HigherOrder (p, k, ins, t) -> HigherOrder (fill_untyped_pi p, fill_untyped_kappa k, fill_untyped_instant ins, fill_untyped_term t)
    | Hiptypes.Shift _ | Hiptypes.Reset _ -> failwith "TODO: shift/reset not supported"
    | Hiptypes.RaisingEff (p, k, ins, t) -> RaisingEff (fill_untyped_pi p, fill_untyped_kappa k, fill_untyped_instant ins, fill_untyped_term t)
    | Hiptypes.TryCatch (p, k, trycatch, t) -> TryCatch (fill_untyped_pi p, fill_untyped_kappa k, fill_untyped_trycatch trycatch, fill_untyped_term t)
  and fill_untyped_spec (spec : Hiptypes.spec) : spec = List.map fill_untyped_spec_stage spec
  and fill_untyped_disj_spec (disj_spec : Hiptypes.disj_spec) : disj_spec = List.map fill_untyped_spec disj_spec
  and fill_untyped_constr_cases (cases : Hiptypes.constr_cases) : constr_cases =
    List.map (fun (name, args, expr) -> (name, List.map binder_of_ident args, fill_untyped_core_lang expr)) cases
  and fill_untyped_try_catch_lemma ((spec, cont, summary) : Hiptypes.tryCatchLemma) : tryCatchLemma =
    (fill_untyped_spec spec, Option.map fill_untyped_disj_spec cont, fill_untyped_disj_spec summary)
  and fill_untyped_core_handler_ops (handlers : Hiptypes.core_handler_ops) : core_handler_ops =
    List.map (fun (name, cont, spec, expr) -> (name, cont, Option.map fill_untyped_disj_spec spec, fill_untyped_core_lang expr)) handlers
  and fill_untyped_core_lang (core_lang : Hiptypes.core_lang) : core_lang =
    let core_desc = match core_lang with
    | Hiptypes.CValue cvalue -> CValue (fill_untyped_term cvalue)
    | Hiptypes.CLet (var, value, expr) -> CLet (var, fill_untyped_core_lang value, fill_untyped_core_lang expr)
    | Hiptypes.CIfELse (cond, then_, else_) -> CIfElse (fill_untyped_pi cond, fill_untyped_core_lang then_, fill_untyped_core_lang else_)
    | Hiptypes.CFunCall (name, args) -> CFunCall (name, List.map fill_untyped_term args)
    | Hiptypes.CWrite (loc, value) -> CWrite (loc, fill_untyped_term value)
    | Hiptypes.CRef value -> CRef (fill_untyped_term value)
    | Hiptypes.CRead loc -> CRead loc
    | Hiptypes.CAssert (p, k) -> CAssert (fill_untyped_pi p, fill_untyped_kappa k)
    | Hiptypes.CPerform (eff, args) -> CPerform (eff, Option.map fill_untyped_term args)
    | Hiptypes.CMatch (handler_type, lemma, scrutinee, fallback, computation_cases, value_cases) ->
        CMatch (handler_type, Option.map fill_untyped_try_catch_lemma lemma, fill_untyped_core_lang scrutinee,
        Option.map (fun (v, expr) -> (binder_of_ident v, fill_untyped_core_lang expr)) fallback,
        fill_untyped_core_handler_ops computation_cases, fill_untyped_constr_cases value_cases)
    | Hiptypes.CResume args -> CResume (List.map fill_untyped_term args)
    | Hiptypes.CLambda (args, spec, body) -> CLambda (List.map binder_of_ident args, Option.map fill_untyped_disj_spec spec, fill_untyped_core_lang body)
    | Hiptypes.CShift _ | Hiptypes.CReset _ -> failwith "TODO"
    in
    {core_desc; core_type = new_type_var ()}
  let fill_untyped_state ((pi, kappa) : Hiptypes.state) : state = (fill_untyped_pi pi, fill_untyped_kappa kappa)
  let fill_untyped_pred_def (d : Hiptypes.pred_def) : pred_def =
    { p_name = Hiptypes.(d.p_name);
      p_params = List.map binder_of_ident Hiptypes.(d.p_params);
      p_body = fill_untyped_disj_spec Hiptypes.(d.p_body);
      p_rec = Hiptypes.(d.p_rec);
    }

  let fill_untyped_lambda_obligation (lo : Hiptypes.lambda_obligation) : lambda_obligation =
    { lo_name = Hiptypes.(lo.lo_name);
      lo_preds = Common.SMap.map fill_untyped_pred_def Hiptypes.(lo.lo_preds);
      lo_left = fill_untyped_disj_spec Hiptypes.(lo.lo_left);
      lo_right = fill_untyped_disj_spec Hiptypes.(lo.lo_right);
    }

  let fill_untyped_meth_def (d : Hiptypes.meth_def) : meth_def =
    { m_name = Hiptypes.(d.m_name);
      m_params = List.map binder_of_ident d.m_params;
      m_spec = Option.map fill_untyped_disj_spec Hiptypes.(d.m_spec);
      m_body = fill_untyped_core_lang Hiptypes.(d.m_body);
      m_tactics = Hiptypes.(d.m_tactics)
    }
  let fill_untyped_sl_pred_def (d : Hiptypes.sl_pred_def) : sl_pred_def =
    { p_sl_ex = List.map binder_of_ident d.p_sl_ex;
      p_sl_name = d.p_sl_name;
      p_sl_params = List.map binder_of_ident d.p_sl_params;
      p_sl_body = fill_untyped_state d.p_sl_body
    }

  let fill_untyped_single_subsumption_obligation (vars, (l, r)) =
    (vars, (fill_untyped_disj_spec l, fill_untyped_disj_spec r))

  let fill_untyped_subsumption_obligation ls =
    List.map fill_untyped_single_subsumption_obligation ls

  let fill_untyped_normal_stage ((evars, pre, post) : Hiptypes.normalStage) : normalStage =
    (List.map binder_of_ident evars, fill_untyped_state pre, fill_untyped_state post)

  let fill_untyped_shift_stage (s : Hiptypes.shiftStage) : shiftStage =
  {
    s_evars = List.map binder_of_ident s.s_evars;
    s_notzero = s.s_notzero;
    s_pre = fill_untyped_state s.s_pre;
    s_post = fill_untyped_state s.s_post;
    s_cont = binder_of_ident s.s_cont;
    s_body = fill_untyped_disj_spec s.s_body;
    s_ret = fill_untyped_term s.s_ret;
  }

  let fill_untyped_reset_stage (r : Hiptypes.resetStage) : resetStage =
  {
    rs_evars = List.map binder_of_ident r.rs_evars;
    rs_pre = fill_untyped_state r.rs_pre;
    rs_post = fill_untyped_state r.rs_post;
    rs_body = fill_untyped_disj_spec r.rs_body;
    rs_ret = fill_untyped_term r.rs_ret;
  }

  let fill_untyped_trycatch_stage (tc : Hiptypes.tryCatchStage) : tryCatchStage =
  {
    tc_evars = List.map binder_of_ident tc.tc_evars;
    tc_pre = fill_untyped_state tc.tc_pre;
    tc_post = fill_untyped_state tc.tc_post;
    tc_constr = fill_untyped_trycatch tc.tc_constr;
    tc_ret = fill_untyped_term tc.tc_ret;
  }

  let fill_untyped_effect_stage (e : Hiptypes.effectStage) : effectStage =
  {
    e_evars = List.map binder_of_ident e.e_evars;
    e_pre = fill_untyped_state e.e_pre;
    e_post = fill_untyped_state e.e_post;
    e_constr = fill_untyped_instant e.e_constr;
    e_ret = fill_untyped_term e.e_ret;
    e_typ = e.e_typ;
  }

  let fill_untyped_eff_ho_trycatch_stage (s : Hiptypes.effHOTryCatchStages) : effHOTryCatchStages =
  match s with
  | Hiptypes.EffHOStage e -> EffHOStage (fill_untyped_effect_stage e)
  | Hiptypes.ShiftStage s -> ShiftStage (fill_untyped_shift_stage s)
  | Hiptypes.TryCatchStage t -> TryCatchStage (fill_untyped_trycatch_stage t)
  | Hiptypes.ResetStage r -> ResetStage (fill_untyped_reset_stage r)

  let fill_normalized_staged_spec ((non_normal, normal): Hiptypes.normalisedStagedSpec) : normalisedStagedSpec =
    List.map fill_untyped_eff_ho_trycatch_stage non_normal, fill_untyped_normal_stage normal


  let fill_untyped_lemma (l : Hiptypes.lemma) : lemma =
  { l_name = l.l_name;
    l_params = List.map binder_of_ident l.l_params;
    l_left = fill_untyped_instant l.l_left;
    l_right = fill_untyped_spec l.l_right
  }

  let fill_untyped_intermediate (i : Hiptypes.intermediate) : intermediate =
    match i with
    | Eff name -> Eff name
    | Lem lemma -> Lem (fill_untyped_lemma lemma)
    | LogicTypeDecl (name, typs, ret_typ, path, lname) ->
        LogicTypeDecl (name, List.map from_hiptypes_typ typs, from_hiptypes_typ ret_typ, path, lname)
    | Meth (name, params, spec, body, tactics, pure_fn_info) ->
        Meth (name, List.map binder_of_ident params, Option.map fill_untyped_disj_spec spec, fill_untyped_core_lang body,
        tactics, Option.map (fun (typs, ret) -> (List.map from_hiptypes_typ typs, from_hiptypes_typ ret)) pure_fn_info)
    | Pred pred_def -> Pred (fill_untyped_pred_def pred_def)
    | SLPred sl_pred_def -> SLPred (fill_untyped_sl_pred_def sl_pred_def)

  let fill_untyped_bindings (bindings : (string * Hiptypes.term) list) : (binder * term) list =
    List.map (fun (b, t) -> (binder_of_ident b, fill_untyped_term t)) bindings
end *)

module Untypehip = struct
  let hiptypes_typ (t : typ) : Hiptypes.typ = t

  let rec untype_term (t : term) : Hiptypes.term =
    match t.term_desc with
    | Const ValUnit -> Const ValUnit
    | Const (Num n) -> Const (Num n)
    | Const (TStr s) -> Const (TStr s)
    | Const TTrue -> Const TTrue
    | Const TFalse -> Const TFalse
    | Const Nil -> Const Nil
    | Var v -> Var v
    | BinOp (Plus, lhs, rhs) -> BinOp (Plus, untype_term lhs, untype_term rhs)
    | BinOp (Minus, lhs, rhs) -> BinOp (Minus, untype_term lhs, untype_term rhs)
    | BinOp (SConcat, lhs, rhs) -> BinOp (SConcat, untype_term lhs, untype_term rhs)
    | BinOp (TAnd, lhs, rhs) -> BinOp (TAnd, untype_term lhs, untype_term rhs)
    | BinOp (TPower, lhs, rhs) -> BinOp (TPower, untype_term lhs, untype_term rhs)
    | BinOp (TTimes, lhs, rhs) -> BinOp (TTimes, untype_term lhs, untype_term rhs)
    | BinOp (TDiv, lhs, rhs) -> BinOp (TDiv, untype_term lhs, untype_term rhs)
    | BinOp (TOr, lhs, rhs) -> BinOp (TOr, untype_term lhs, untype_term rhs)
    | BinOp (TCons, lhs, rhs) -> BinOp (TCons, untype_term lhs, untype_term rhs)
    | Rel (op, lhs, rhs) -> Rel (op, untype_term lhs, untype_term rhs)
    | TNot t -> TNot (untype_term t)
    | TApp (f, args) -> TApp (f, List.map untype_term args)
    | TLambda (id, params, spec, body) ->
        TLambda (id, List.map ident_of_binder params, Option.map untype_staged_spec spec,
                 Option.map untype_core_lang body)
    | TList ts -> TList (List.map untype_term ts)
    | TTuple ts -> TTuple (List.map untype_term ts)
  and untype_pi (p : pi) : Hiptypes.pi =
    match p with
    | True -> Hiptypes.True
    | False -> Hiptypes.False
    | Atomic (op, t1, t2) -> Hiptypes.Atomic (op, untype_term t1, untype_term t2)
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
    | CMatch (ht, trycatch_opt, scrutinee, value_case, handler_cases, constr_cases) ->
        let trycatch_opt' = Option.map untype_tryCatchLemma trycatch_opt in
        let value_case' = Option.map (fun (v, e) -> (ident_of_binder v, untype_core_lang e)) value_case in
        let handler_cases' = untype_handler_ops handler_cases in
        let constr_cases' = untype_constr_cases constr_cases in
        CMatch (ht, trycatch_opt', untype_core_lang scrutinee, value_case', handler_cases', constr_cases')
    | CResume vs -> CResume (List.map untype_term vs)
    | CLambda (params, spec, body) ->
        CLambda (List.map ident_of_binder params, Option.map untype_staged_spec spec, untype_core_lang body)
    | CShift (is_shift, x, body) ->
        CShift (is_shift, ident_of_binder x, untype_core_lang body)
    | CReset e -> CReset (untype_core_lang e)
  and untype_handler_ops (ops : core_handler_ops) : Hiptypes.core_handler_ops =
    List.map (fun (label, k_opt, spec, body) -> (label, k_opt, Option.map untype_staged_spec spec, untype_core_lang body)) ops
  and untype_constr_cases (cases : constr_cases) : Hiptypes.constr_cases =
    List.map (fun (name, args, body) -> (name, List.map ident_of_binder args, untype_core_lang body)) cases
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
  | Exists (xs, f) -> Hiptypes.Exists (xs, untype_staged_spec f)
  | Require (phi, h) ->
      Hiptypes.Require (untype_pi phi, untype_kappa h)
  | NormalReturn (phi, h) ->
      Hiptypes.NormalReturn (untype_pi phi, untype_kappa h)
  | HigherOrder (f, t) ->
      Hiptypes.HigherOrder (f, List.map untype_term t)
  | Shift (is_shift, x, spec) ->
      Hiptypes.Shift (is_shift, x, untype_staged_spec spec)
  | Disjunction (f1, f2) ->
      Hiptypes.Disjunction (untype_staged_spec f1, untype_staged_spec f2)
  | Sequence (f1, f2) ->
      Hiptypes.Sequence (untype_staged_spec f1, untype_staged_spec f2)
  | Bind (x, f1, f2) ->
      Hiptypes.Bind (x, untype_staged_spec f1, untype_staged_spec f2)
  | Reset (spec) ->
      Hiptypes.Reset (untype_staged_spec spec)
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

  (* let untype_sl_pred_def (d : sl_pred_def) : Hiptypes.sl_pred_def =
    let (phi, h) = d.p_sl_body in
    {
      Hiptypes.p_sl_ex = List.map ident_of_binder d.p_sl_ex;
      Hiptypes.p_sl_name = d.p_sl_name;
      Hiptypes.p_sl_params = List.map ident_of_binder d.p_sl_params;
      Hiptypes.p_sl_body = (untype_pi phi, untype_kappa h);
    }

  let untype_meth_def (d : meth_def) : Hiptypes.meth_def =
    { Hiptypes.m_name = d.m_name;
      Hiptypes.m_params = List.map ident_of_binder d.m_params;
      Hiptypes.m_spec = Option.map untype_disj_spec d.m_spec;
      Hiptypes.m_body = untype_core_lang d.m_body;
      Hiptypes.m_tactics = d.m_tactics
    }

  let untype_pred_def (d : pred_def) : Hiptypes.pred_def =
    {
      Hiptypes.p_name = d.p_name;
      Hiptypes.p_params = List.map ident_of_binder d.p_params;
      Hiptypes.p_body = untype_disj_spec d.p_body;
      Hiptypes.p_rec = d.p_rec;
    }

  let untype_lemma (l : lemma) : Hiptypes.lemma =
    {
      Hiptypes.l_name = l.l_name;
      Hiptypes.l_params = (List.map ident_of_binder l.l_params);
      Hiptypes.l_left = untype_instant l.l_left;
      Hiptypes.l_right = untype_spec l.l_right;
    }

  let untype_intermediate (i : intermediate) : Hiptypes.intermediate =
    match i with
    | Eff name -> Hiptypes.Eff name
    | Lem lemma -> Hiptypes.Lem (untype_lemma lemma)
    | LogicTypeDecl (name, typs, ret_typ, path, lname) ->
        Hiptypes.LogicTypeDecl (name, List.map hiptypes_typ typs, hiptypes_typ ret_typ, path, lname)
    | Meth (name, params, spec, body, tactics, pure_fn_info) ->
        Hiptypes.Meth (
          name,
          List.map ident_of_binder params,
          Option.map untype_disj_spec spec,
          untype_core_lang body,
          tactics,
          Option.map (fun (ts, t) -> (List.map hiptypes_typ ts, hiptypes_typ t)) pure_fn_info
        )
    | Pred def -> Hiptypes.Pred (untype_pred_def def)
    | SLPred def -> Hiptypes.SLPred (untype_sl_pred_def def)

  let untype_core_program (prog : core_program) : Hiptypes.core_program = {
    cp_effs = prog.cp_effs;
    cp_predicates = Common.SMap.map untype_pred_def (prog.cp_predicates);
    cp_sl_predicates = Common.SMap.map untype_sl_pred_def (prog.cp_sl_predicates);
    cp_lemmas = Common.SMap.map untype_lemma (prog.cp_lemmas);
    cp_methods = List.map untype_meth_def (prog.cp_methods)
  }

  let untype_normal_stage ((evars, pre, post) : normalStage) : Hiptypes.normalStage =
    (List.map ident_of_binder evars, untype_state pre, untype_state post)

  let untype_shift_stage (s : shiftStage) : Hiptypes.shiftStage =
  {
    s_evars = List.map ident_of_binder s.s_evars;
    s_notzero = s.s_notzero;
    s_pre = untype_state s.s_pre;
    s_post = untype_state s.s_post;
    s_cont = ident_of_binder s.s_cont;
    s_body = untype_disj_spec s.s_body;
    s_ret = untype_term s.s_ret;
  }

  let untype_reset_stage (r : resetStage) : Hiptypes.resetStage =
  {
    rs_evars = List.map ident_of_binder r.rs_evars;
    rs_pre = untype_state r.rs_pre;
    rs_post = untype_state r.rs_post;
    rs_body = untype_disj_spec r.rs_body;
    rs_ret = untype_term r.rs_ret;
  }

  let untype_trycatch_stage (tc : tryCatchStage) : Hiptypes.tryCatchStage =
  {
    Hiptypes.tc_evars = List.map ident_of_binder tc.tc_evars;
    tc_pre = untype_state tc.tc_pre;
    tc_post = untype_state tc.tc_post;
    tc_constr = untype_trycatch tc.tc_constr;
    tc_ret = untype_term tc.tc_ret;
  }

  let untype_effect_stage (e : effectStage) : Hiptypes.effectStage =
  {
    Hiptypes.e_evars = List.map ident_of_binder e.e_evars;
    e_pre = untype_state e.e_pre;
    e_post = untype_state e.e_post;
    e_constr = untype_instant e.e_constr;
    e_ret = untype_term e.e_ret;
    e_typ = e.e_typ;
  }

  let untype_eff_ho_trycatch_stage (s : effHOTryCatchStages) : Hiptypes.effHOTryCatchStages =
  match s with
  | EffHOStage e -> Hiptypes.EffHOStage (untype_effect_stage e)
  | ShiftStage s -> Hiptypes.ShiftStage (untype_shift_stage s)
  | TryCatchStage t -> Hiptypes.TryCatchStage (untype_trycatch_stage t)
  | ResetStage r -> Hiptypes.ResetStage (untype_reset_stage r)

  let untype_normalized_staged_spec ((non_normal, normal): normalisedStagedSpec) : Hiptypes.normalisedStagedSpec =
    List.map untype_eff_ho_trycatch_stage non_normal, untype_normal_stage normal

  let untype_pure_fn_def (d : pure_fn_def) : Hiptypes.pure_fn_def = {
      pf_name = d.pf_name;
      pf_params = List.map (fun (name, typ) -> (name, hiptypes_typ typ)) d.pf_params;
      pf_ret_type = hiptypes_typ d.pf_ret_type;
      pf_body = untype_core_lang d.pf_body
    }

  let untype_pure_fn_type_def (d : pure_fn_type_def) : Hiptypes.pure_fn_type_def = {
    pft_name = d.pft_name;
    pft_logic_path = d.pft_logic_path;
    pft_logic_name = d.pft_logic_name;
    pft_params = List.map hiptypes_typ d.pft_params;
    pft_ret_type = hiptypes_typ d.pft_ret_type;
  } *)

  let untype_bindings (bindings : (binder * term) list) : (string * Hiptypes.term) list =
    List.map (fun (b, t) -> (ident_of_binder b, untype_term t)) bindings

  (* let untype_type_env_map (env : Hiptypes.TMap.t) : TMap.t = *)
  (*   ref (TMap.bindings !env) *)
end

type 'a quantified = binder list * 'a
