
open Common

include Untyped_core_ast
(* not part of the visitor because this doesn't occur recursively *)

open Types

[@@@warning "+17"]

(*

let z3_consumption = ref 0.0
let summary_forward = ref 0.0
let summary_entail = ref 0.0
let summary_storing_spec = ref 0.0
let summary_askZ3 = ref 0.0

*)

module U = struct
  include UnionFind

  let merge f a b = ignore (merge f a b)
end


(*

(* [@@@warning "-17"]

type effectStage = {
  e_evars : string list;
  e_pre : pi * kappa;
  e_post : pi * kappa;
  e_constr : instant;
  e_ret : term;
  e_typ : [`Eff | `Fn] [@opaque];
}
[@@deriving
  visitors { variety = "map"; name = "map_effect_stage_" },
  visitors { variety = "reduce"; name = "reduce_effect_stage_" }]

type shiftStage = {
  s_evars : string list;
  s_notzero : bool;
  s_pre : pi * kappa;
  s_post : pi * kappa;
  s_cont : string;
  s_body : disj_spec;
  s_ret : term;
}
[@@deriving
  visitors { variety = "map"; name = "map_shift_stage_" },
  visitors { variety = "reduce"; name = "reduce_shift_stage_" }]

type resetStage = {
  rs_evars : string list;
  rs_pre : pi * kappa;
  rs_post : pi * kappa;
  rs_body : disj_spec;
  rs_ret : term;
}
[@@deriving
  visitors { variety = "map"; name = "map_reset_stage_" },
  visitors { variety = "reduce"; name = "reduce_reset_stage_" }]

type tryCatchStage = {
  tc_evars : string list;
  tc_pre : pi * kappa;
  tc_post : pi * kappa;
  tc_constr : trycatch;
  tc_ret : term;
}
[@@deriving
  visitors { variety = "map"; name = "map_try_catch_stage_" },
  visitors { variety = "reduce"; name = "reduce_try_catch_stage_" }]


type effHOTryCatchStages =
  | EffHOStage of effectStage
  | ShiftStage of shiftStage
  | TryCatchStage of tryCatchStage
  | ResetStage of resetStage
[@@deriving
  visitors { variety = "map"; name = "map_eff_stages_" },
  visitors { variety = "reduce"; name = "reduce_eff_stages_" }]

(** existentials, pre, post (which may contain constraints on res) *)
type normalStage =  (string list* (pi * kappa ) * (pi * kappa))
[@@deriving
  visitors { variety = "map"; name = "map_normal_stages_" },
  visitors { variety = "reduce"; name = "reduce_normal_stages_" }]

type normalisedStagedSpec = effHOTryCatchStages list * normalStage
[@@deriving
  visitors { variety = "map"; name = "map_normalised_" },
  visitors { variety = "reduce"; name = "reduce_normalised_" }]

[@@@warning "+17"]

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

let freshNormalReturnSpec = [NormalReturn (True, EmptyHeap)]
let freshNormalStage : normalStage = ([], (True, EmptyHeap), (True, EmptyHeap))

let freshNormStageRet r : normalStage = ([], (True, EmptyHeap), (res_eq r, EmptyHeap))

let counter_4_inserting_let_bindings = ref 0  *)
*)

type tactic =
  | Unfold_right
  | Unfold_left
  | Apply of string
  | Case of int * tactic

type meth_def = {
  m_name : string;
  m_params : string list;
  m_spec : staged_spec option;
  m_body : core_lang;
  m_tactics : tactic list;
}

(** A predicate is a name for a parameterized disjunctive staged spec of the form [f(x, ...) == spec \/ ...].
    Predicates are checked or inferred for effectful functions and remembered after. *)
type pred_def = {
  p_name: string;
  p_params: string list; (* list to ensure ordering. last param is typically a return value *)
  p_body: staged_spec;
  p_rec: bool;
}

type sl_pred_def = {
  p_sl_ex: string list;
  p_sl_name: string;
  p_sl_params: string list; (* list to ensure ordering. last param is typically a return value *)
  p_sl_body: pi * kappa;
}

(** A pure function that can be imported directly into SMT *)
type pure_fn_def = {
  pf_name: string;
  pf_params: (string * typ) list;
  pf_ret_type: typ;
  pf_body: core_lang;
}

type pure_fn_type_def = Types.pure_fn_type_def

(** A lemma is an entailment [f(x, ...) <: spec]. The left side is restricted to be a function stage (without loss of generality). Some of x, ... may be parameters, but some may not be. *)
type lemma = {
  l_name: string;
  l_params: string list;
  l_left: staged_spec;
  l_right: staged_spec;
}

type lambda_obligation = {
  lo_name: string;
  lo_preds: pred_def SMap.t;
  lo_left: staged_spec;
  lo_right: staged_spec;
}

type intermediate =
  | Eff of string
  | Lem of lemma
  (* type definition of pure logic function *)
  | LogicTypeDecl of string * typ list * typ * string list * string
  (* name, params, spec, body, tactics, pure_fn_info *)
  | Meth of string * string list * staged_spec option * core_lang * tactic list * (typ list * typ) option
  (* user-provided type definition *)
  | Typedef of type_declaration
  | Pred of pred_def
  | SLPred of sl_pred_def

type core_program = {
  cp_effs: string list;
  cp_predicates: pred_def SMap.t;
  cp_sl_predicates: sl_pred_def SMap.t;
  cp_lemmas: lemma SMap.t;
  cp_methods: meth_def list;
}

let empty_program = {
  cp_effs = [];
  cp_methods = [];
  cp_predicates = SMap.empty;
  cp_sl_predicates = SMap.empty;
  cp_lemmas = SMap.empty
}

include Common

type 'a quantified = string list * 'a

type instantiations = (string * string) list

let primitive_functions = ["+"; "-"; "*"; "="; "not"; "::"; "&&"; "||"; ">"; "<"; ">="; "<="; "^"; "string_of_int"]
