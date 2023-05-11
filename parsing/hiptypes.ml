
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
      (* this constructor is also used for inductive predicate applications *)
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

type tactic =
  | Unfold_right
  | Unfold_left
  | Apply of string

type meth_def = {
  m_name : string;
  m_params : string list;
  m_spec : spec list;
  m_body : core_lang;
  m_tactics : tactic list;
}
(* type eff_def = string *)

(** a lemma is a formula such as f$(a, r) |= c(a, r) *)
type lemma = {
  l_name : string;
  (* l_params : string list; *)
  l_left : stagedSpec;
  l_right : spec;
}

type pred_def = {
  p_name: string;
  p_params: string list;
  p_body: disj_spec;
}

type core_program = {
  cp_effs: string list;
  cp_predicates: pred_def list;
  cp_lemmas: lemma list;
  cp_methods: meth_def list;
}

let rec split_last xs =
  match xs with
  | [] -> failwith "split_last"
  | [x] -> ([], x)
  | x :: xs ->
    let init, last = split_last xs in
    (x :: init, last)