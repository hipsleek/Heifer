
open Hipcore_typed.Typedhip
open Hipcore_typed.Pretty

let config = default_config |> set_single_line

type 'a proof_log =
  | Step of 'a
  | Subproof of 'a proof_log list

(* a zipper over a proof log *)
type 'a partial_proof_log = {
  current_proof : 'a proof_log list;
  parent_env : 'a partial_proof_log option
}

let empty_partial_log = {current_proof = []; parent_env = None}

let proof_step s = Step s

let append ppl step =
  { ppl with current_proof = step :: ppl.current_proof }

let open_subproof ppl = {
  current_proof = [];
  parent_env = Some ppl
}

let close_subproof ppl = 
  let parent_env = Option.get ppl.parent_env in
  let current_proof = Subproof (List.rev ppl.current_proof) :: parent_env.current_proof in
  { parent_env with current_proof }

let rec finalize_proof_log ppl =
  match ppl.parent_env with
  | None -> Subproof (List.rev ppl.current_proof)
  | Some _ -> finalize_proof_log (close_subproof ppl)

let rec string_of_proof_log ?(indent = 0) log string_of_step =
  let indent_string = String.init indent (Fun.const ' ') in
  match log with
  | Step s -> indent_string ^ (string_of_step s) ^ "\n"
  | Subproof steps ->
      indent_string ^ "{\n" ^ 
      (steps |> List.map (fun s -> string_of_proof_log ~indent:(indent + 2) s string_of_step) |> String.concat "") ^
      indent_string ^ "}\n"

let%expect_test "proof logging" =
  let output_log log = 
    Printf.printf "%s\n" (string_of_proof_log log Fun.id)
  in 
  let log = empty_partial_log in
  let log = append log (proof_step "intros.") in
  let log = append log (proof_step "split.") in
  let log = open_subproof log in
    let log = append log (proof_step "exfalso.") in
    let log = append log (proof_step "assumption.") in
  let log = close_subproof log in
  let log = open_subproof log in
    let log = append log (proof_step "auto.") in
  let log = close_subproof log in
  output_log (finalize_proof_log log);
  [%expect {|
    {
      intros.
      split.
      {
        exfalso.
        assumption.
      }
      {
        auto.
      }
    }
    |}];;
  


type constr = CVar of string
  | CConst of const
  | CApp of constr * constr list
  | CFun of string * constr
  (* these are only to make the output look nicer *)
  | CInfix of constr * string * constr
  | CSurround of string * constr * string
  (* invalid node, meant to allow for better context regarding incomplete constr generation *)
  | CError of string
  | CQuantify of string * string list * constr

(* Do not throw an exception when processing an invalid node. Instead, return a CError. *)

let pi_mentions_result p = Hipcore_typed.(Syntax.conjuncts_of_pi p |> List.exists Variables.is_eq_res)

let rec hprop_of_kappa (k : kappa) : constr =
  match k with
  | SepConj (k1, k2) -> CInfix (hprop_of_kappa k1, "\\*", hprop_of_kappa k2)
  | EmptyHeap -> CVar "\\[]"
  | PointsTo (l, v) -> CInfix (CVar l, "~~>", constr_of_term v)
and constr_of_term (t : term) : constr =
  match t.term_desc with
  | Const c -> CConst c
  | Var v -> CVar v
  | TNot t -> CApp (CVar "vnot", [constr_of_term t])
  | BinOp (op, lhs, rhs) ->
      let op_fun = match op with
        | Plus -> CVar "vplus"
        | _ -> CError "[binary operation]"
      in
      CApp (op_fun, [constr_of_term lhs; constr_of_term rhs])
  | _ -> CError (string_of_term ~config t)
and constr_of_pi (p : pi) : constr =
  match p with
  | True -> CVar "True"
  | False -> CVar "False"
  | And (lhs, rhs) -> CInfix (constr_of_pi lhs, "/\\", constr_of_pi rhs)
  | Or (lhs, rhs) -> CInfix (constr_of_pi lhs, "\\/", constr_of_pi rhs)
  | Imply (lhs, rhs) -> CInfix (constr_of_pi lhs, "->", constr_of_pi rhs)
  | Atomic (op, lhs, rhs) ->
      (* if this is a result comparison, insert a cast to [val] *)
      begin
      match Hipcore_typed.Variables.eq_res_term p with
      | Some t -> CInfix (CVar "res", "=", CApp (CVar "into", [constr_of_term t]))
      | None ->
        (* NOTE: these are currently implemented to only compare integers! *)
        let operator = match op with
          | EQ -> "="
          | GT -> ">"
          | LT -> "<"
          | GTEQ -> ">="
          | LTEQ -> "<="
        in
        CInfix (constr_of_term lhs, operator, constr_of_term rhs)
      end
  | Not p -> CSurround ("~", constr_of_pi p, "")
  | _ -> CError (string_of_pi ~config p)
and constr_of_state ((p, k) : state) =
  CInfix (hprop_of_kappa k, "\\*", CSurround ("\\[", constr_of_pi p, "]"))
and constr_of_staged_spec (ss : staged_spec) : constr =
  match ss with
  | Exists (v, ss) -> CApp (CVar "fex", [CFun (ident_of_binder v, constr_of_staged_spec ss)])
  | ForAll (v, ss) -> CApp (CVar "fall", [CFun (ident_of_binder v, constr_of_staged_spec ss)])
  | Require (p, k) -> CApp (CVar "req_", [constr_of_state (p, k)])
  (* support only one argument for now, pack multiple arguments via vtup...? *)
  | HigherOrder (f, [arg]) -> CApp (CVar "unk", [CConst (TStr f); constr_of_term arg])
  (* need to convert anything that says nothing about the result to an [ens_] ... *)
  | NormalReturn (p, k) -> 
      if pi_mentions_result p
      then CApp (CVar "ens", [CFun ("res", constr_of_state (p, k))])
      else CApp (CVar "ens_", [constr_of_state (p, k)])
  | Sequence (Require (p, k), f) -> CApp (CVar "req", [constr_of_state (p, k); constr_of_staged_spec f])
  | Sequence (f1, f2) -> CInfix (constr_of_staged_spec f1, ";;", constr_of_staged_spec f2)
  | Disjunction (f1, f2) -> CApp (CVar "disj", [constr_of_staged_spec f1; constr_of_staged_spec f2])
  | Bind (v, f1, f2) -> 
      let bind f fk = match type_of_binder v with
        | Int -> CApp (CVar "@bind_t", [CVar "int"; CVar "_"; f; fk])
        | TConstr ("ref", _) -> CApp (CVar "@bind_t", [CVar "loc"; CVar "_"; f; fk])
        (* let Coq infer the underlying type *)
        (* if the bound variable is unused, it infers Int, which breaks some of the rewriting rules *)
        (* there might need to be a better special case for that scenario... *)
        | _ -> CApp (CVar "bind_t", [f; fk])
      in
      bind (constr_of_staged_spec f1) (CFun (ident_of_binder v, constr_of_staged_spec f2))
  | _ -> CError (string_of_staged_spec ~config ss)

let rec string_of_constr c =
  match c with
  | CConst c -> begin match c with
    | ValUnit -> "vunit"
    | TStr s -> "\"" ^ s ^ "\""
    | Num n -> string_of_int n
    | Nil -> "[]"
    | TTrue -> "true"
    | TFalse -> "false"
    end
  | CVar v -> v
  | CFun (x, body) -> Printf.sprintf "(fun %s => %s)" x (string_of_constr body)
  | CApp (f, args) -> Printf.sprintf "(%s %s)" (string_of_constr f) (List.map string_of_constr args |> String.concat " ")
  | CInfix (lhs, op, rhs) -> Printf.sprintf "(%s %s %s)" (string_of_constr lhs) op (string_of_constr rhs)
  | CSurround (lp, sub, rp) -> Printf.sprintf "%s %s %s" lp (string_of_constr sub) rp
  | CError s -> Printf.sprintf "(* unsupported node: %s *) _" s
  | CQuantify (q, vars, body) -> Printf.sprintf "%s %s, %s" q (String.concat " " vars) (string_of_constr body)

let quantify vars constr =
  match vars with
  | [] -> constr
  | free_vars -> CQuantify ("forall", free_vars, constr)

let remove_nonterm_variables free_var_mapping =
  free_var_mapping
  |> Utils.Hstdlib.SMap.to_list
  |> List.filter_map (fun (fv, ty) ->
      match ty with
      | None -> None
      | Some _ -> Some fv)

(* TODO quantify all free vars *)
let statement_of_entailment f1 f2 = 
  let free_vars = 
    let open Utils.Hstdlib in
    let open Hipcore_typed.Subst in
    SMap.merge_arbitrary (types_of_free_vars Sctx_staged f1) (types_of_free_vars Sctx_staged f2)
    |> SMap.remove "res"
    |> remove_nonterm_variables
  in
  (* Printf.printf "SOE fv [%s] end\n" (String.concat "; " free_vars); *)
  let entailment = CApp (CVar "entails", [constr_of_staged_spec f1; constr_of_staged_spec f2]) in
  quantify free_vars entailment

let statement_of_method name params spec =
  match params with
  | [p] -> 
    let free_vars =
      let open Hipcore_typed.Subst in
      let open Utils.Hstdlib in
      types_of_free_vars Sctx_staged spec
      |> SMap.add (ident_of_binder p) (Some (type_of_binder p))
      |> remove_nonterm_variables
    in
    (* Printf.printf "SOM %s fv [%s] end\n" name (String.concat "; " free_vars); *)
    CQuantify ("forall", free_vars,
    CApp (CVar "entails", [CApp (CVar "unk", [CConst (TStr name); CVar (ident_of_binder p)]); constr_of_staged_spec spec]))
  | _ -> CError ("unsupported method " ^ name)

type certificate_file = out_channel

let make_certificate_file out =
  let prelude = {|
From ShiftReset Require Import Logic Entl Automation Norm Propriety.
From ShiftReset.Mechanized Require Import State Normalization Entail_tactics.

Local Open Scope string_scope.

(* Due to deficiencies in the underlying model, this is necessary to get some of the
  needed rewrite operations (in particular, those manipulating the body of a [bind])
  to succeed. If this admit is undesired, it may be possible to prove the needed instances
  of RewritableBinder individually. *)

#[global]
Instance RewritableBinder_anything : forall f, RewritableBinder f.
Proof.
Admitted.

(* primitive function declarations *)

Definition vplus (a b:val) : val :=
  match a, b with
  | vint a, vint b => vint (a + b)
  | _, _ => vunit
  end.

(* end prelude *)

|}
  in
  Printf.fprintf out "%s" prelude;
  out

let write_theorem ~out ~program ~name ~statement ~string_of_step log =
  (* Printf.printf "writing theorem for %s\n" name; *)
  (* Printf.printf "statement: %s\n" (string_of_constr statement); *)
  let theorem_params =
    program.cp_predicates
    |> Utils.Hstdlib.SMap.to_list
    |> List.map (fun (_, pred_def) -> 
        let statement = statement_of_method pred_def.p_name pred_def.p_params pred_def.p_body in
        Printf.sprintf "(%s_rewrite_rule : %s)" pred_def.p_name (string_of_constr statement))
  in
  Printf.fprintf out "(* begin proof item %s *)\n" name;
  Printf.fprintf out "Theorem %s %s\n : %s.\n" name (String.concat "\n  " theorem_params) (string_of_constr statement);
  Printf.fprintf out "Proof. intros. rew_hprop_to_state.\n";
  begin match log with
  | None -> Printf.fprintf out "Admitted.\n"
  | Some log -> Printf.fprintf out "%s" (string_of_proof_log log string_of_step);
    Printf.fprintf out "Qed.\n"
  end;
  Printf.fprintf out "(* end proof item %s *)\n\n" name;
  Out_channel.flush out
  
let write_assumption ~out ~name ~statement =
  Printf.fprintf out "Parameter %s: %s.\n\n" name (string_of_constr statement);
  Out_channel.flush out;
