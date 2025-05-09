
[@@@warning "-17"]
type bin_rel_op = [%import: Hiptypes.bin_op]
and binder = string * typ
and bin_term_op = Plus | Minus | SConcat | TAnd | TPower | TTimes | TDiv | TOr | TCons
and const = 
  | Unit
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
  | TLambda of string * binder list * disj_spec * core_lang option
  (* unused *)
  | TList of term list
  | TTuple of term list
and term =
  {
    term_desc: term_desc;
    term_type: typ
  }
(* (Label n) _k (*@ spec @*) -> e *)
and core_handler_ops = (string * string option * disj_spec option * core_lang) list

(* x :: xs -> e is represented as ("::", [x, xs], e) *)
and constr_cases = (string * string list * core_lang) list

and tryCatchLemma = (spec * disj_spec option * (*(handlingcases) **) disj_spec) (*tcl_head, tcl_handledCont, tcl_summary*)

and handler_type = [%import : Hiptypes.handler_type]

and core_lang_desc = 
      | CValue of core_value 
      | CLet of string * core_lang * core_lang
      | CIfElse of (*core_value*) pi * core_lang * core_lang
      | CFunCall of string * (core_value) list
      | CWrite of string * core_value  
      | CRef of core_value
      | CRead of string 
      | CAssert of pi * kappa 
      | CPerform of string * core_value option
      (* match e with | v -> e1 | eff case... | constr case... *)
      | CMatch of handler_type * tryCatchLemma option * core_lang * (string * core_lang) option * core_handler_ops * constr_cases
      | CResume of core_value list
      | CLambda of binder list * disj_spec option * core_lang
      | CShift of bool * string * core_lang (* bool=true is for shift, and bool=false for shift0 *)
      | CReset of core_lang

and core_lang =
  {core_desc: core_lang_desc;
   core_type: typ}
and core_value = term
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
  | PointsTo of (string * term)
  | SepConj of kappa * kappa
  (*| MagicWand of kappa * kappa*)

(* a formula which describes a program state *)
and state = pi * kappa

(* v->phi and (Eff arg?-> phi)* *)
and handlingcases = (string * disj_spec) * ((string * string option * disj_spec) list)
and trycatch = (spec * handlingcases)


and stagedSpec = 
      | Exists of binder list
      | Require of (pi * kappa)
      (* ens H /\ P, where P may contain contraints on res *)
      | NormalReturn of (pi * kappa)
      (* higher-order functions: H /\ P /\ f$(...args, term) *)
      (* this constructor is also used for inductive predicate applications *)
      (* f$(x, y) is HigherOrder(..., ..., (f, [x]), y) *)
      | HigherOrder of (pi * kappa * instant * term)
      | Shift of bool * string * disj_spec * term (* see CShift for meaning of bool *)
      | Reset of disj_spec * term
      (* effects: H /\ P /\ E(...args, v), term is always a placeholder variable *)
      | RaisingEff of (pi * kappa * instant * term)
      (* | IndPred of { name : string; args: term list } *)
      | TryCatch of (pi * kappa * trycatch * term)

and spec = stagedSpec list

and disj_spec = spec list

and typ =
  | TyUnit
  | Int
  | Bool
  | TyString
  | Lamb
  | Arrow of typ * typ
  | TConstr of string * typ list (* TConstr ("ty", [a; b]) => (a, b) ty *)
  (* TODO Add this: | Poly of string list * typ (* Poly (["a", "b"], ty) ==> 'a 'b. ty *) *)
  | TVar of string (* this is last, so > concrete types *)

[@@deriving
  visitors { variety = "map"; name = "map_spec" },
  visitors { variety = "reduce"; name = "reduce_spec" } ]

type tactic = Hiptypes.tactic

type sl_pred_def = {
  p_sl_ex: string list;
  p_sl_name: string;
  p_sl_params: string list; (* list to ensure ordering. last param is typically a return value *)
  p_sl_body: pi * kappa;
}

type pred_def = {
  p_name: string;
  p_params: string list; (* list to ensure ordering. last param is typically a return value *)
  p_body: disj_spec;
  p_rec: bool;
}

type lemma = {
  l_name: string;
  l_params: string list; (* ordered, the last parameter is a result *)
  l_left: instant; (* for simplicity of rewriting *)
  l_right: spec; (* could also be disj_spec but not needed *)
}

type intermediate =
  | Eff of string
  | Lem of lemma
  | LogicTypeDecl of string * typ list * typ * string list * string
  (* name, params, spec, body, tactics, pure_fn_info *)
  | Meth of string * string list * disj_spec option * core_lang * tactic list * (typ list * typ) option
  | Pred of pred_def
  | SLPred of sl_pred_def

let new_type_var : ?name:string -> unit -> typ =
  let counter = ref 0 in begin
  fun ?(name="") () ->
    counter := !counter + 1;
    TVar (if name = "" then "[tvar " ^ string_of_int !counter ^ "]" else name)
  end

let binder_of_ident ?(typ=new_type_var ()) (ident : string) : binder =
  (ident, typ)

let ident_of_binder ((name, _) : binder) = name

(* Modules regarding converting a Typedhip AST to a Hiptypes AST and vice versa.
   There may be interest in using an Untypeast-like API for this instead, to allow
   for extensibility. *)

module Fill_type = struct
  (** Module for transforming a Hiptypes AST element into a Typedhip element.
      All types are filled in with placeholders, to be populated during typechecking. Since
      there are utilities that take the Typedtree as input, most program types should be coming from
      the OCaml typechecker; this is used to typecheck annotations.*)

  let rec fill_untyped_term (term : Hiptypes.term) =
    let term_desc = match term with
    | Hiptypes.UNIT -> Const Unit
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
    | Hiptypes.CMatch _ -> failwith "TODO"
    | Hiptypes.CResume _ -> failwith "TODO"
    | Hiptypes.CLambda (args, spec, body) -> CLambda (List.map binder_of_ident args, Option.map fill_untyped_disj_spec spec, fill_untyped_core_lang body)
    | Hiptypes.CShift _ | Hiptypes.CReset _ -> failwith "TODO"
    in
    {core_desc; core_type = new_type_var ()}
end

module Untypehip = struct
  let rec hiptypes_typ (t : typ) : Hiptypes.typ =
    match t with
    | TyUnit -> Hiptypes.Unit
    | Int -> Hiptypes.Int
    | Bool -> Hiptypes.Bool
    | TyString -> Hiptypes.TyString
    | Lamb -> Hiptypes.Lamb
    | Arrow (a, b) -> Hiptypes.Arrow (hiptypes_typ a, hiptypes_typ b)
    | TVar s -> Hiptypes.TVar s
    | _ -> failwith "Type not represented in original type"

  let rec untype_term (t : term) : Hiptypes.term =
    match t.term_desc with
    | Const Unit -> UNIT
    | Const (Num n) -> Num n
    | Const (TStr s) -> TStr s
    | Const TTrue -> TTrue
    | Const TFalse -> TFalse
    | Const Nil -> Nil
    | Var v -> Var v
    | BinOp (Plus, lhs, rhs) -> Plus (untype_term lhs, untype_term rhs)
    | BinOp (Minus, lhs, rhs) -> Minus (untype_term lhs, untype_term rhs)
    | BinOp (SConcat, lhs, rhs) -> SConcat (untype_term lhs, untype_term rhs)
    | BinOp (TAnd, lhs, rhs) -> TAnd (untype_term lhs, untype_term rhs)
    | BinOp (TPower, lhs, rhs) -> TPower (untype_term lhs, untype_term rhs)
    | BinOp (TTimes, lhs, rhs) -> TTimes (untype_term lhs, untype_term rhs)
    | BinOp (TDiv, lhs, rhs) -> TDiv (untype_term lhs, untype_term rhs)
    | BinOp (TOr, lhs, rhs) -> TOr (untype_term lhs, untype_term rhs)
    | BinOp (TCons, lhs, rhs) -> TCons (untype_term lhs, untype_term rhs)
    | Rel (op, lhs, rhs) -> Rel (op, untype_term lhs, untype_term rhs)
    | TNot t -> TNot (untype_term t)
    | TApp (f, args) -> TApp (f, List.map untype_term args)
    | TLambda (id, params, spec, body) ->
        TLambda (id, List.map ident_of_binder params, untype_disj_spec spec,
                 Option.map untype_core_lang body)
    | TList ts -> TList (List.map untype_term ts)
    | TTuple ts -> TTupple (List.map untype_term ts)
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
    | CLet (x, e1, e2) -> CLet (x, untype_core_lang e1, untype_core_lang e2)
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
        let value_case' = Option.map (fun (v, e) -> (v, untype_core_lang e)) value_case in
        let handler_cases' = untype_handler_ops handler_cases in
        let constr_cases' = untype_constr_cases constr_cases in
        CMatch (ht, trycatch_opt', untype_core_lang scrutinee, value_case', handler_cases', constr_cases')
    | CResume vs -> CResume (List.map untype_term vs)
    | CLambda (params, spec, body) ->
        CLambda (List.map ident_of_binder params, Option.map untype_disj_spec spec, untype_core_lang body)
    | CShift (is_shift, x, body) ->
        CShift (is_shift, x, untype_core_lang body)
    | CReset e -> CReset (untype_core_lang e)
  and untype_handler_ops (ops : core_handler_ops) : Hiptypes.core_handler_ops =
    List.map (fun (label, k_opt, spec, body) -> (label, k_opt, Option.map untype_disj_spec spec, untype_core_lang body)) ops
  and untype_constr_cases (cases : constr_cases) : Hiptypes.constr_cases =
    List.map (fun (name, args, body) -> (name, args, untype_core_lang body)) cases
  and untype_tryCatchLemma (tcl : tryCatchLemma) : Hiptypes.tryCatchLemma =
    let (head, handled_cont, summary) = tcl in
    (untype_spec head, Option.map untype_disj_spec handled_cont, untype_disj_spec summary)
  and untype_handlingcases (((placeholder, disj_spec), effs) : handlingcases) : Hiptypes.handlingcases =
    ((placeholder, untype_disj_spec disj_spec), List.map (fun (name, arg, disj_spec) ->
      (name, arg, untype_disj_spec disj_spec)) effs)
  and untype_trycatch ((spec, cases) : trycatch) : Hiptypes.trycatch =
    (untype_spec spec, untype_handlingcases cases)
  and untype_instant ((eff_name, args) : instant) : Hiptypes.instant =
    (eff_name, List.map untype_term args)
  and untype_staged_spec (s : stagedSpec) : Hiptypes.stagedSpec =
  match s with
  | Exists xs -> Hiptypes.Exists (List.map ident_of_binder xs)
  | Require (phi, h) ->
      Hiptypes.Require (untype_pi phi, untype_kappa h)
  | NormalReturn (phi, h) ->
      Hiptypes.NormalReturn (untype_pi phi, untype_kappa h)
  | HigherOrder (phi, h, inst, t) ->
      Hiptypes.HigherOrder (untype_pi phi, untype_kappa h, untype_instant inst, untype_term t)
  | Shift (is_shift, x, spec, t) ->
      Hiptypes.Shift (is_shift, x, untype_disj_spec spec, untype_term t)
  | Reset (spec, t) ->
      Hiptypes.Reset (untype_disj_spec spec, untype_term t)
  | RaisingEff (phi, h, inst, t) ->
      Hiptypes.RaisingEff (untype_pi phi, untype_kappa h, untype_instant inst, untype_term t)
  | TryCatch (phi, h, tc, t) ->
      Hiptypes.TryCatch (untype_pi phi, untype_kappa h, untype_trycatch tc, untype_term t)
  and untype_spec spec = List.map untype_staged_spec spec
  and untype_disj_spec spec = List.map untype_spec spec

  let untype_sl_pred_def (d : sl_pred_def) : Hiptypes.sl_pred_def =
    let (phi, h) = d.p_sl_body in
    {
      Hiptypes.p_sl_ex = d.p_sl_ex;
      Hiptypes.p_sl_name = d.p_sl_name;
      Hiptypes.p_sl_params = d.p_sl_params;
      Hiptypes.p_sl_body = (untype_pi phi, untype_kappa h);
    }

  let untype_pred_def (d : pred_def) : Hiptypes.pred_def =
    {
      Hiptypes.p_name = d.p_name;
      Hiptypes.p_params = d.p_params;
      Hiptypes.p_body = untype_disj_spec d.p_body;
      Hiptypes.p_rec = d.p_rec;
    }

  let untype_lemma (l : lemma) : Hiptypes.lemma =
    {
      Hiptypes.l_name = l.l_name;
      Hiptypes.l_params = l.l_params;
      Hiptypes.l_left = untype_instant l.l_left;
      Hiptypes.l_right = untype_spec l.l_right;
    }

  let untype_intermediate (i : intermediate) : Hiptypes.intermediate =
    match i with
    | Eff name -> Hiptypes.Eff name
    | Lem lemma -> Hiptypes.Lem (untype_lemma lemma)
    | LogicTypeDecl (name, typs, ret_typ, classes, doc) ->
        Hiptypes.LogicTypeDecl (name, List.map hiptypes_typ typs, hiptypes_typ ret_typ, classes, doc)
    | Meth (name, params, spec, body, tactics, pure_fn_info) ->
        Hiptypes.Meth (
          name,
          params,
          Option.map untype_disj_spec spec,
          untype_core_lang body,
          tactics,
          Option.map (fun (ts, t) -> (List.map hiptypes_typ ts, hiptypes_typ t)) pure_fn_info
        )
    | Pred def -> Hiptypes.Pred (untype_pred_def def)
    | SLPred def -> Hiptypes.SLPred (untype_sl_pred_def def)
end
