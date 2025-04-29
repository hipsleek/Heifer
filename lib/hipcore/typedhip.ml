
[@@@warning "-17"]
type bin_op = [%import: Hiptypes.bin_op]
and binder = string * typ
and term_desc =
  | Unit
  | Num of int
  | Var of string
  | TStr of string
  | Plus of term * term 
  | Minus of term * term 
  | SConcat of term * term 
  | Rel of bin_op * term * term 
  | TTrue
  | TFalse
  | TAnd of term * term
  | TPower of term * term
  | TTimes of term * term
  | TDiv of term * term
  | TOr of term * term
  | TNot of term
  | TApp of string * term list
  | TCons of term * term
  | Nil
  (* the string is just an identifier for uniqueness.
     the last param is the name of the result *)
  | TLambda of string * binder list * disj_spec * core_lang option
  (* unused *)
  | TList of term list
  | TTupple of term list
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

and handler_type = Shallow | Deep 

and core_lang_desc = 
      | CValue of core_value 
      | CLet of string * core_lang * core_lang
      | CIfELse of (*core_value*) pi * core_lang * core_lang
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
  | Atomic of bin_op * term * term
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
  | Ref of typ
  | TVar of string (* this is last, so > concrete types *)
[@@deriving
  visitors { variety = "map"; name = "map_spec" },
  visitors { variety = "reduce"; name = "reduce_spec" } ]

type tactic =
  | Unfold_right
  | Unfold_left
  | Apply of string
  | Case of int * tactic

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
    | Hiptypes.UNIT -> Unit
    | Hiptypes.Num n -> Num n
    | Hiptypes.Var v -> Var v
    | Hiptypes.TStr s -> TStr s
    | Hiptypes.Plus (lhs, rhs) -> Plus (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.Minus (lhs, rhs) -> Minus (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.SConcat (lhs, rhs) -> SConcat (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.Rel (op, lhs, rhs) -> Rel (op, fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TTrue -> TTrue
    | Hiptypes.TFalse -> TFalse
    | Hiptypes.TAnd (lhs, rhs) -> TAnd (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TPower (lhs, rhs) -> TAnd (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TTimes (lhs, rhs) -> TTimes (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TDiv (lhs, rhs) -> TDiv (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TOr (lhs, rhs) -> TOr (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.TNot t -> TNot (fill_untyped_term t)
    | Hiptypes.TApp (f, args) -> TApp (f, List.map fill_untyped_term args)
    | Hiptypes.TCons (lhs, rhs) -> TCons (fill_untyped_term lhs, fill_untyped_term rhs)
    | Hiptypes.Nil -> Nil
    | Hiptypes.TLambda (id, params, spec, body) -> TLambda (id, List.map binder_of_ident params, fill_untyped_disj_spec spec, Option.map fill_untyped_core_lang body)
    | Hiptypes.TList ts -> TList (List.map fill_untyped_term ts)
    | Hiptypes.TTupple ts -> TTupple (List.map fill_untyped_term ts)
    in
    {term_desc; term_type = new_type_var ()}
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
    | Hiptypes.CIfELse (cond, then_, else_) -> CIfELse (fill_untyped_pi cond, fill_untyped_core_lang then_, fill_untyped_core_lang else_)
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
