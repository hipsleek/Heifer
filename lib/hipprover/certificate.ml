
open Hipcore_typed.Typedhip

exception Unsupported_term of string

type constr = CVar of string
  | CConst of const
  | CApp of constr * constr list
  | CFun of string * constr
  (* these are only to make the output look nicer *)
  | CInfix of constr * string * constr
  | CSurround of string * constr * string

let rec hprop_of_kappa (k : kappa) : constr =
  match k with
  | SepConj (k1, k2) -> CInfix (hprop_of_kappa k1, "\\*", hprop_of_kappa k2)
  | EmptyHeap -> CVar "hempty"
  | PointsTo (l, v) -> CInfix (CVar l, "~~>", constr_of_term v)
and constr_of_term (t : term) : constr =
  match t.term_desc with
  | Const c -> CConst c
  | Var v -> CVar v
  | _ -> failwith "TODO a proper failure wrapper"
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
        | _ -> failwith "TODO a proper failure wrapper"
      in
      CInfix (constr_of_term lhs, operator, constr_of_term rhs)
  | _ -> failwith "TODO a proper failure wrapper"
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
  | Bind (v, f1, f2) -> CApp (CVar "bind", [constr_of_staged_spec f1; CFun (ident_of_binder v, constr_of_staged_spec f2)])
  | _ -> failwith "TODO a proper failure wrapper"

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


let finalize_proof_log ppl =
  match ppl.parent_env with
  | None -> Subproof ppl.current_proof
  | Some _ -> failwith "Attempt to finalize unfinished proof log"

let rec close_all_subproofs ppl =
  match ppl.parent_env with
  | None -> ppl
  | Some _ -> close_all_subproofs (close_subproof ppl)
