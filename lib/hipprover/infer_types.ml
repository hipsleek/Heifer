open Hipcore
open Hiptypes
open Types
open Pretty
open Debug

(* record the type (or constraints on) of a program variable in the environment *)
let assert_var_has_type v t env =
  match SMap.find_opt v env.vartypes with
  | None -> { env with vartypes = SMap.add v t env.vartypes }
  | Some t1 ->
    if
      TEnv.has_concrete_type env.equalities t
      && TEnv.has_concrete_type env.equalities t1
    then (
      let t' = TEnv.concretize env.equalities t in
      let t1' = TEnv.concretize env.equalities t1 in
      match t1 with       (* ASK Darius *)
      | TVar _ -> ()      (* ASK Darius *)
      | _ ->              (* ASK Darius *)
      if compare_typ t' t1' <> 0 then
        failwith
          (Format.asprintf "%s already has type %s but was used as type %s" v
             (string_of_type t1) (string_of_type t)))
    else TEnv.equate env.equalities t1 t;
    env

(* record a (nontrivial) equality in the environment *)
let unify_types t1 t2 env =
  debug ~at:5 ~title:"unify" "%s ~ %s" (string_of_type t1) (string_of_type t2);
  if compare_typ t1 t2 = 0 then env
  else (
    if
      TEnv.has_concrete_type env.equalities t1
      && TEnv.has_concrete_type env.equalities t2
    then (
      let t1 = TEnv.concretize env.equalities t1 in
      let t2 = TEnv.concretize env.equalities t1 in
      if compare_typ t1 t2 <> 0 then
        failwith
          (Format.asprintf "%s ~/~ %s"
             (string_of_type (TEnv.concretize env.equalities t1))
             (string_of_type (TEnv.concretize env.equalities t2))))
    else TEnv.equate env.equalities t1 t2;
    env)

let find_concrete_type = TEnv.concretize

let concrete_type_env abs : typ_env =
  SMap.map
    (fun v ->
      match v with TVar _ ->
        (* Format.printf "%s@." (string_of_type v); *)
        find_concrete_type abs.equalities v | _ -> v)
    abs.vartypes

let get_primitive_type f =
  (* let untype = Typedhip.Untypehip.hiptypes_typ in *)
  match f with
  | "cons" -> ([Int; List_int], List_int)
  | "head" -> ([List_int], Int)
  | "tail" -> ([List_int], List_int)
  | "is_nil" | "is_cons" -> ([List_int], Bool)
  | "+" | "-" -> ([Int; Int], Int)
  | "string_of_int" -> ([Int], TyString)
  | _ when String.compare f "effNo" == 0 -> ([Int] , Int)
  | _ when Globals.is_pure_fn_defined f ->
    let fn = Globals.pure_fn f in
    (List.map snd fn.pf_params, fn.pf_ret_type)
  | _ when SMap.mem f Globals.global_environment.pure_fn_types ->
    let fn = SMap.find f Globals.global_environment.pure_fn_types in
    (fn.pft_params, fn.pft_ret_type)
  | _ ->
      failwith (Format.asprintf "unknown function 2: %s" f)

let get_primitive_fn_type f =
  match f with
  | "=" -> ([Int; Int], Bool)
  | _ -> failwith (Format.asprintf "unknown function: %s" f)

let rec infer_types_core_lang env e =
  match e with
  | CValue t -> infer_types_term env t
  | CFunCall (f, args) ->
    let ex_args, ex_ret = get_primitive_fn_type f in
    let _arg_types, env =
    List.fold_right2 (fun arg ex_arg (t, env) ->
      let inf_arg, env = infer_types_term env arg in
      let env = unify_types inf_arg ex_arg env in
      inf_arg :: t, env
      ) args ex_args ([], env)
    in
    ex_ret, env
  | CLet (x, e1, e2) ->
    let t1, env = infer_types_core_lang env e1 in
    let env = assert_var_has_type x t1 env in
    infer_types_core_lang env e2
  | CSequence (e1, e2) ->
    let _t1, env = infer_types_core_lang env e1 in
    infer_types_core_lang env e2
  | CIfELse (_, _, _) -> failwith "CIfELse"
  | CWrite (_, _) -> failwith "CWrite"
  | CRef _ -> failwith "CRef"
  | CRead _ -> failwith "CRead"
  | CAssert (_, _) -> failwith "CAssert"
  | CPerform (_, _) -> failwith "CPerform"
  | CMatch (_, _, _, _, _, _) -> failwith "CMatch"
  | CResume _ -> failwith "CResume"
  | CShift (_, _, _) | CReset _
  | CLambda (_, _, _) ->
    failwith "not implemented"

and infer_types_term ?(hint : typ option) (env : abs_typ_env) term : typ * abs_typ_env =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:5 ~title:"infer_types" "%s : %s -| %s" (string_of_term term)
          (string_of_result string_of_type (map_presult fst r))
          (string_of_result string_of_abs_env (map_presult snd r)))
  in
  match (term, hint) with
  | Const ValUnit, _ -> (Unit, env)
  | Const TTrue, _ | Const TFalse, _ -> (Bool, env)
  | Const (TStr _), _ -> (TyString, env)
  | TNot a, _ ->
    let _at, env1 = infer_types_term ~hint:(Bool) env a in
    (Bool, env1)
  | BinOp (TAnd, a, b), _ ->
    let _at, env = infer_types_term ~hint:(Bool) env a in
    let _bt, env = infer_types_term ~hint:(Bool) env b in
    (Bool, env)
  | BinOp (TOr, a, b), _ ->
    let _at, env = infer_types_term ~hint:(Bool) env a in
    let _bt, env = infer_types_term ~hint:(Bool) env b in
    (Bool, env)
  | Const Nil, _ -> (List_int, env)
  | BinOp (TCons, a, b), _ ->
    let _at, env1 = infer_types_term ~hint:(Int) env a in
    let _bt, env2 = infer_types_term ~hint:(List_int) env1 b in
    (List_int, env2)
  | Const (Num _), _ -> (Int, env)
  (* possibly add syntactic heuristics for types, such as names *)
  | Var v, Some t -> (t, assert_var_has_type v t env)
  | Var v, None ->
    let t = (TVar (Variables.fresh_variable v)) in
    (t, assert_var_has_type v t env)
  | TLambda (_, _, _, Some _), _
  | TLambda (_, _, _, None), _ -> ((Lamb), env)
  (* | TLambda (_, params, _, Some b), _ ->
    (* TODO use the spec? *)
    (try
      let params, _ret = unsnoc params in
      let ptvs = List.map (fun _ -> TVar (verifier_getAfreeVar "param")) params in
      let env = List.fold_right2 (fun p pt env -> assert_var_has_type p pt env) params ptvs env in
      let ty_ret, env = infer_types_core_lang env b in
      let ty = List.fold_right (fun c t -> Arrow (c, t)) ptvs ty_ret in
      ty, env
    with Failure _ ->
      (* if inferring types for the body fails (likely due to the types of impure stuff not being representable), fall back to old behavior for now *)
      Lamb, env) *)
  | Rel (EQ, a, b), _ -> begin
    try
      let at, env1 = infer_types_term ~hint:(Int) env a in
      let bt, env2 = infer_types_term ~hint:(Int) env1 b in
      let env3 = unify_types at bt env2 in
      ((Bool), env3)
    with _ ->
      let _bt, env1 = infer_types_term ~hint:(Int) env b in
      let _at, env2 = infer_types_term ~hint:(Int) env1 a in
      ((Bool), env2)
  end
  | Rel ((GT | LT | GTEQ | LTEQ), a, b), _ ->
    let _at, env1 = infer_types_term ~hint:(Int) env a in
    let _bt, env2 = infer_types_term ~hint:(Int) env1 b in
    ((Bool), env2)
  | BinOp (SConcat, a, b), _ ->
    let _at, env1 = infer_types_term ~hint:(TyString) env a in
    let _bt, env2 = infer_types_term ~hint:(TyString) env1 b in
    ((TyString), env2)
  | BinOp (Plus, a, b), _ | BinOp (Minus, a, b), _ | BinOp (TPower, a, b), _ | BinOp (TTimes, a, b), _ | BinOp (TDiv, a, b), _ ->
    let _at, env1 = infer_types_term ~hint:(Int) env a in
    let _bt, env2 = infer_types_term ~hint:(Int) env1 b in
    ((Int), env2)
  | TApp (f, args), _ ->
    let argtypes, ret = get_primitive_type f in
    let env =
      List.map2 (fun x y -> x, y) args argtypes |>
        (* infer from right to left *)
        List.fold_left
          (fun env (a, at) ->
            let _, env = infer_types_term ~hint:at env a in
            env)
          env
    in
    (ret, env)
  | TTuple _, _ -> failwith "tuple unimplemented"

let rec infer_types_pi env pi =
  (* let@ _ =
       Debug.span (fun r ->
           debug ~at:5 ~title:"infer_types_pi" "%s -| %s" (string_of_pi pi)
             (string_of_result string_of_abs_env r))
     in *)
  match pi with
  | True | False -> env
  | Atomic (EQ, a, b) ->
    let t1, env = infer_types_term env a in
    let t2, env = infer_types_term env b in
    (* Format.printf "EQ %s = %s@." (string_of_term a) (string_of_term b); *)
    let env = unify_types t1 t2 env in
    env
  | Atomic (GT, a, b)
  | Atomic (LT, a, b)
  | Atomic (GTEQ, a, b)
  | Atomic (LTEQ, a, b) -> begin
    let _t, env = infer_types_term ~hint:(Int) env a in
    let _t, env = infer_types_term ~hint:(Int) env b in
    env
  end
  | And (a, b) | Or (a, b) | Imply (a, b) ->
    let env = infer_types_pi env a in
    let env = infer_types_pi env b in
    env
  | Not a -> infer_types_pi env a
  | Predicate (_, _) -> env
  | Subsumption (_, _) -> env
