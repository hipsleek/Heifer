
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
      (* common *)
      | Exists of (string list)
      | Require of pi * kappa 
      | NormalReturn of (pi * kappa * term) (* H /\ Pure /\ res=term *)
      (* higher-order functions *)
      (* | HigherOrder of (string * term list) *)
      | HigherOrder of (pi * kappa * instant * term)
      (* effects *)
      | RaisingEff of (pi * kappa * instant * term) (* term is a placeholder for the resumed value, pi/\kappa is the state before the perform *)


type effectStage =  (string list* (pi * kappa ) * (pi * kappa) * instant * term)
type normalStage =  (string list* (pi * kappa ) * (pi * kappa) * term)

type normalisedStagedSpec = effectStage list * normalStage

let freshNormalReturnSpec = [NormalReturn (True, EmptyHeap, UNIT)]
let freshNoramlStage : normalStage = ([], (True, EmptyHeap), (True, EmptyHeap), UNIT) 

(* type linearStagedSpec = stagedSpec list *)

(* type spec = (pi * linearStagedSpec) list  *)
type spec = stagedSpec list 

type core_value = term

type core_handler_ops = (string * string * core_lang) list

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
type core_program = string list * meth_def list