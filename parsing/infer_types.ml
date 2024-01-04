open Hipcore
open Hiptypes
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
      match v with TVar _ -> find_concrete_type abs.equalities v | _ -> v)
    abs.vartypes

let get_primitive_type f =
  match f with
  | "cons" -> ([Int; List_int], List_int)
  | "head" -> ([List_int], Int)
  | "tail" -> ([List_int], List_int)
  | "is_nil" | "is_cons" -> ([List_int], Bool)
  | "+" | "-" -> ([Int; Int], Int)
  | _ when String.compare f "effNo" == 0 -> ([Int] , Int)
  | _ when Globals.is_pure_fn_defined f ->
    let fn = Globals.pure_fn f in
    (List.map snd fn.pf_params, fn.pf_ret_type)
  | _ ->
      failwith (Format.asprintf "unknown function 2: %s" f)

let rec infer_types_term ?hint (env : abs_typ_env) term : typ * abs_typ_env =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:5 ~title:"infer_types" "%s : %s -| %s" (string_of_term term)
          (string_of_result string_of_type (Option.map fst r))
          (string_of_result string_of_abs_env (Option.map snd r)))
  in
  match (term, hint) with
  | UNIT, _ -> (Unit, env)
  | TTrue, _ | TFalse, _ -> (Bool, env)
  | TNot a, _ ->
    let _at, env1 = infer_types_term ~hint:Bool env a in
    (Bool, env1)
  | TAnd (a, b), _ ->
    let _at, env = infer_types_term ~hint:Bool env a in
    let _bt, env = infer_types_term ~hint:Bool env b in
    (Bool, env)
  | TOr (a, b), _ ->
    let _at, env = infer_types_term ~hint:Bool env a in
    let _bt, env = infer_types_term ~hint:Bool env b in
    (Bool, env)
  | Nil, _ -> (List_int, env)
  | TCons (a, b), _ ->
    let _at, env1 = infer_types_term ~hint:Int env a in
    let _bt, env2 = infer_types_term ~hint:List_int env1 b in
    (List_int, env2)
  | Num _, _ -> (Int, env)
  (* possibly add syntactic heuristics for types, such as names *)
  | Var v, Some t -> (t, assert_var_has_type v t env)
  | Var v, None ->
    let t = TVar (verifier_getAfreeVar v) in
    (t, assert_var_has_type v t env)
  | TLambda _, _ -> (Lamb, env)
  | Rel (EQ, a, b), _ -> begin
    try
      let at, env1 = infer_types_term ~hint:Int env a in
      let bt, env2 = infer_types_term ~hint:Int env1 b in
      let env3 = unify_types at bt env2 in
      (Bool, env3)
    with _ ->
      let _bt, env1 = infer_types_term ~hint:Int env b in
      let _at, env2 = infer_types_term ~hint:Int env1 a in
      (Bool, env2)
  end
  | Rel ((GT | LT | GTEQ | LTEQ), a, b), _ ->
    let _at, env1 = infer_types_term ~hint:Int env a in
    let _bt, env2 = infer_types_term ~hint:Int env1 b in
    (Bool, env2)
  | Plus (a, b), _ | Minus (a, b), _ | TPower (a, b), _ | TTimes (a, b), _ | TDiv (a, b), _ ->
    let _at, env1 = infer_types_term ~hint:Int env a in
    let _bt, env2 = infer_types_term ~hint:Int env1 b in
    (Int, env2)
  | TApp (f, args), _ ->
    let argtypes, ret = get_primitive_type f in
    let env =
      (* infer from right to left *)
      List.fold_left
        (fun env (a, at) ->
          let _, env = infer_types_term ~hint:at env a in
          env)
        env
        (List.map2 pair args argtypes)
    in
    (ret, env)
  | TList _, _ | TTupple _, _ -> failwith "list/tuple unimplemented"

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
    let _t, env = infer_types_term ~hint:Int env a in
    let _t, env = infer_types_term ~hint:Int env b in
    env
  end
  | And (a, b) | Or (a, b) | Imply (a, b) ->
    let env = infer_types_pi env a in
    let env = infer_types_pi env b in
    env
  | Not a -> infer_types_pi env a
  | Predicate (_, _) -> env (*failwith "not implemented" *)
