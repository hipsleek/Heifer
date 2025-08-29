(** Definitions which are not part of the core recursive AST loop, and can
 therefore be defined in a separate module. *)

open Utils.Hstdlib

module Make(M : Ast.AST) = struct
  type meth_def = {
    m_name: string;
    m_params: M.binder list;
    m_spec: M.staged_spec option;
    m_body: M.core_lang;
    m_tactics: Tactics.tactic list;
  }

  type pred_def = {
    p_name: string;
    p_params: M.binder list;
    p_body: M.staged_spec;
    p_rec: bool
  }

  type sl_pred_def = {
    p_sl_ex: M.binder list;
    p_sl_name: string;
    p_sl_params: M.binder list;
    p_sl_body: M.state;
  }

  type pure_fn_def = {
    pf_name: string;
    pf_params: M.binder list;
    pf_ret_type: Types.typ;
    pf_body: M.core_lang;
  }

  type lemma = {
    l_name: string;
    l_params: M.binder list;
    l_left: M.staged_spec;
    l_right: M.staged_spec;
  }

  type lambda_obligation = {
    lo_name: string;
    lo_preds: pred_def SMap.t;
    lo_left: M.staged_spec;
    lo_right: M.staged_spec;
  }

  type intermediate =
    | Eff of string
    | Lem of lemma
    (* type definition of pure logic function *)
    | LogicTypeDecl of string * Types.typ list * Types.typ * string list * string
    (* name, params, spec, body, tactics, pure_fn_info *)
    | Meth of string * M.binder list * M.staged_spec option * M.core_lang * Tactics.tactic list * (Types.typ list * Types.typ) option
    (* user-provided type definition *)
    | Typedef of Types.type_declaration
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
end
