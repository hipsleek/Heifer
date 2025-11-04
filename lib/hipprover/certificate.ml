
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

type constr = CVar of string
  | CConst of const
  | CApp of constr * constr list
  | CFun of string * constr
  (* these are only to make the output look nicer *)
  | CInfix of constr * string * constr
  | CSurround of string * constr * string
  (* invalid node, meant to allow for better context regarding incomplete constr generation *)
  | CError of string

(* Do not throw an exception when processing an invalid node. Instead, return a CError. *)

let rec hprop_of_kappa (k : kappa) : constr =
  match k with
  | SepConj (k1, k2) -> CInfix (hprop_of_kappa k1, "\\*", hprop_of_kappa k2)
  | EmptyHeap -> CVar "\\[]"
  | PointsTo (l, v) -> CInfix (CVar l, "~~>", constr_of_term v)
and constr_of_term (t : term) : constr =
  match t.term_desc with
  | Const c -> CConst c
  | Var v -> CVar v
  | _ -> CError (string_of_term ~config t)
and constr_of_pi (p : pi) : constr =
  match p with
  | True -> CVar "True"
  | False -> CVar "False"
  | And (lhs, rhs) -> CInfix (constr_of_pi lhs, "/\\", constr_of_pi rhs)
  | Or (lhs, rhs) -> CInfix (constr_of_pi lhs, "\\/", constr_of_pi rhs)
  | Imply (lhs, rhs) -> CInfix (constr_of_pi lhs, "->", constr_of_pi rhs)
  | Atomic (op, lhs, rhs) ->
      let operator = match op with
        | EQ -> "="
        | GT -> ">"
        | LT -> "<"
        | GTEQ -> ">="
        | LTEQ -> "<="
      in
      CInfix (constr_of_term lhs, operator, constr_of_term rhs)
  | _ -> CError (string_of_pi ~config p)
and constr_of_state ((p, k) : state) =
  CInfix (hprop_of_kappa k, "\\*", CSurround ("\\[", constr_of_pi p, "]"))
and constr_of_staged_spec (ss : staged_spec) : constr =
  match ss with
  | Exists (v, ss) -> CApp (CVar "fex", [CFun (ident_of_binder v, constr_of_staged_spec ss)])
  | ForAll (v, ss) -> CApp (CVar "fall", [CFun (ident_of_binder v, constr_of_staged_spec ss)])
  | Require (p, k) -> CApp (CVar "req_", [constr_of_state (p, k)])
  (* need to convert anything that says nothing about the result to an [ens_] ... *)
  | NormalReturn (p, k) -> CApp (CVar "ens", [CFun ("res", constr_of_state (p, k))])
  | Sequence (f1, f2) -> CInfix (constr_of_staged_spec f1, ";;", constr_of_staged_spec f2)
  | Disjunction (f1, f2) -> CApp (CVar "disj", [constr_of_staged_spec f1; constr_of_staged_spec f2])
  | Bind (v, f1, f2) -> CApp (CVar "bind_t", [constr_of_staged_spec f1; CFun (ident_of_binder v, constr_of_staged_spec f2)])
  | _ -> CError (string_of_staged_spec ~config ss)

let rec string_of_constr c =
  match c with
  | CConst c -> begin match c with
    | ValUnit -> "tt"
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

let statement_of_entailment f1 f2 = CApp (CVar "entails", [constr_of_staged_spec f1; constr_of_staged_spec f2])

type certificate_file = out_channel

let make_certificate_file out =
  let prelude = {|
From ShiftReset Require Import Logic Entl Automation Norm Propriety.
From ShiftReset.Mechanized Require Import State Normalization Entail_tactics.

(* Due to deficiencies in the underlying model, this is necessary to get some of the
  needed rewrite operations (in particular, those manipulating the body of a [bind])
  to succeed. If this admit is undesired, it may be possible to prove the needed instances
  of RewritableBinder individually. *)

#[global]
Instance RewritableBinder_anything : forall f, RewritableBinder f.
Proof.
Admitted.

(* end prelude *)

|}
  in
  Printf.fprintf out "%s" prelude;
  out

let write_theorem ~out ~name ~statement ~string_of_step log =
  Printf.fprintf out "(* begin proof item %s *)\n" name;
  Printf.fprintf out "Theorem %s : %s.\n" name (string_of_constr statement);
  Printf.fprintf out "Proof. rew_hprop_to_state.\n";
  begin match log with
  | None -> Printf.fprintf out "Admitted.\n"
  | Some log -> Printf.fprintf out "%s" (string_of_proof_log log string_of_step);
    Printf.fprintf out "Qed.\n"
  end;
  Printf.fprintf out "(* end proof item %s *)\n\n" name;
  Out_channel.flush out
  

