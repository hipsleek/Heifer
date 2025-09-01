open Hipcore

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
  | PointsTo of string * term
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
  | Shift of bool * binder * staged_spec * binder * staged_spec (* see CShift for meaning of bool *)
  | Reset of staged_spec
  | Sequence of staged_spec * staged_spec
  | Bind of binder * staged_spec * staged_spec
  | Disjunction of staged_spec * staged_spec
  (* effects: H /\ P /\ E(...args, v), term is always a placeholder variable *)
  | RaisingEff of (pi * kappa * instant * term)
  (* | IndPred of { name : string; args: term list } *)
  | TryCatch of (pi * kappa * trycatch * term)
(* copied here so visitors can be generated *)
and typ = Types.typ = 
  | Any
  | Unit
  | Int
  | Bool
  | TyString
  | Lamb
  | Arrow of typ * typ
  | TConstr of string * typ list
  | TVar of string

[@@deriving
  visitors { variety = "map"; name = "map_spec" },
  visitors { variety = "reduce"; name = "reduce_spec" },
  visitors { variety = "mapreduce"; name = "mapreduce_spec" },
  ord]
