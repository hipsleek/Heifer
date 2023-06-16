
module SSet = struct
  include Set.Make (String)
  let concat sets = List.fold_right union sets empty
end

module SMap = struct
  include Map.Make (String)
end

type term =
    | UNIT 
    | Num of int
    | Var of string
    | Plus of term * term 
    | Minus of term * term 
    | Eq of term * term 
    | TTrue
    | TFalse
    | TApp of string * term list
    | Nil
    (* unused *)
    | TList of term list
    | TTupple of term list

let term_cons c t = TApp ("cons", [c; t])

type typ =
  | Unit
  | List_int
  | Int
  | Bool
  | TVar of string

type abs_typ_env = {
  vartypes: typ SMap.t;
  eqs: (typ * typ) list
}

let create_abs_env () =
  {
    vartypes = SMap.empty; eqs = []
  }

type typ_env = typ SMap.t

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
      (* this constructor is also used for inductive predicate applications *)
      (* f$(x, y) is HigherOrder(..., ..., (f, [x]), y) *)
      | HigherOrder of (pi * kappa * instant * term)
      (* effects: H /\ P /\ E(...args, v), term is always a placeholder variable *)
      | RaisingEff of (pi * kappa * instant * term)
      (* | IndPred of { name : string; args: term list } *)

(* type spec = (pi * linearStagedSpec) list  *)
type spec = stagedSpec list
type disj_spec = spec list

(* type effectStage =  (string list* (pi * kappa ) * (pi * kappa) * instant * term) *)
type effectStage = {
  e_evars : string list;
  e_pre : pi * kappa;
  e_post : pi * kappa;
  e_constr : instant;
  e_ret : term;
  e_typ : [`Eff | `Fn];
}

type normalStage =  (string list* (pi * kappa ) * (pi * kappa) * term)

type normalisedStagedSpec = effectStage list * normalStage

let freshNormalReturnSpec = [NormalReturn (True, EmptyHeap, UNIT)]
let freshNormalStage : normalStage = ([], (True, EmptyHeap), (True, EmptyHeap), UNIT) 

let freshNormStageVar v : normalStage = ([v], (True, EmptyHeap), (True, EmptyHeap), Var v) 

let freshNormStageRet r : normalStage = ([], (True, EmptyHeap), (True, EmptyHeap), r) 

(* type linearStagedSpec = stagedSpec list *)

type core_value = term

(* (Label n) _k -> e *)
type core_handler_ops = (string * string option * core_lang) list

(* x :: xs -> e is represented as ("::", [x, xs], e) *)
and constr_cases = (string * string list * core_lang) list

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
      (* match e with | v -> e1 | eff case... | constr case... *)
      | CMatch of core_lang * (string * core_lang) option * core_handler_ops * constr_cases
      | CResume of core_value 

type tactic =
  | Unfold_right
  | Unfold_left
  | Apply of string
  | Case of int * tactic

type meth_def = {
  m_name : string;
  m_params : string list;
  m_spec : disj_spec option;
  m_body : core_lang;
  m_tactics : tactic list;
}
(* type eff_def = string *)

(** A predicate is a name for a parameterized disjunctive spec, of the form [f(x, ...) == spec \/ ...], where x, ... are all parameters *)
type pred_def = {
  p_name: string;
  p_params: string list; (* list to ensure ordering. last param is typically a return value *)
  p_body: disj_spec;
}

(** A lemma is an entailment [f(x, ...) <: spec]. The left side restricted to be a function stage (without loss of generality). Some of x, ... may be parameters, but some may not be. *)
type lemma = {
  l_name: string;
  l_params: string list; (* ordered *)
  l_left: instant; (* for simplicity of rewriting *)
  l_right: spec; (* could also be disj_spec but not needed *)
}

type core_program = {
  cp_effs: string list;
  cp_predicates: pred_def SMap.t;
  cp_lemmas: lemma SMap.t;
  cp_methods: meth_def list;
}

include Common

type 'a quantified = string list * 'a

type instantiations = (string * string) list