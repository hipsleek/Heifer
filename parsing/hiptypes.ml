
type term = 
    | UNIT 
    | Num of int
    | TList of (term list)
    | TTupple of (term list)
    | Var of string
    | Plus of term * term 
    | Minus of term * term 

(* an occurrence of an effect *)
type instant = string * term list


type bin_op = GT | LT | EQ | GTEQ | LTEQ

type pi = 
  | True
  | False
  | Atomic of bin_op * term * term
  | And    of pi * pi
  | Or     of pi * pi
  | Imply  of pi * pi
  | Not    of pi 
  | Predicate of string * term

type kappa = 
  | EmptyHeap
    (* x -> -   means x is allocated, and - is encoded as Var "_" *)
  | PointsTo of (string * term)
  | SepConj of kappa * kappa
  (*| MagicWand of kappa * kappa*)

(* a formula which describes a program state *)
type state = pi * kappa

type stagedSpec = 
      | Exists of string list
      | Require of pi * kappa 
      (* H /\ P /\ res=term *)
      | NormalReturn of (pi * kappa * term)
      (* higher-order functions: H /\ P /\ f$(...args, term) *)
      | HigherOrder of (pi * kappa * instant * term)
      (* effects: H /\ P /\ E(...args, v), term is always a placeholder variable *)
      | RaisingEff of (pi * kappa * instant * term)
      | Pred of { vars: string list }

(* type spec = (pi * linearStagedSpec) list  *)
type spec = stagedSpec list (* disjunctive *)

type effectStage =  (string list* (pi * kappa ) * (pi * kappa) * instant * term)
type normalStage =  (string list* (pi * kappa ) * (pi * kappa) * term)

type normalisedStagedSpec = effectStage list * normalStage

let freshNormalReturnSpec = [NormalReturn (True, EmptyHeap, UNIT)]
(* let freshNormalStage : normalStage = ([], (True, EmptyHeap), (True, EmptyHeap), UNIT)  *)

let freshNormStageVar v : normalStage = ([v], (True, EmptyHeap), (True, EmptyHeap), Var v) 

(* type linearStagedSpec = stagedSpec list *)


type core_value = term

(* (Label n) _k -> e *)
type core_handler_ops = (string * string option * core_lang) list

and core_lang = 
      | CValue of core_value 
      | CLet of string * core_lang * core_lang
      | CIfELse of core_value * core_lang * core_lang
      | CFunCall of string * (core_value) list
      | CWrite of string * core_value  
      | CRef of core_value
      | CRead of string 
      | CAssert of pi * kappa 
      | CPerform of string * core_value option
      | CMatch of core_lang * (string * core_lang) * core_handler_ops
      | CResume of core_value 

type meth_def = string * (string list) * (spec list) * core_lang
(* type eff_def = string *)

type pred_def = {
  p_name: string;
  p_vars: string;
  p_body: spec;
}

type core_program = {
  cp_effs: string list;
  cp_preds: pred_def list;
  cp_methods: meth_def list;
}