open Hipcore
open Hiptypes
open Pretty

(* let main () =
   TEnv.equate (TVar "a") Int;
   TEnv.equate (TVar "c") (TVar "a");
   let t3 = TEnv.concretize (TVar "c") in

   (* let b = Int.elt 1 in *)
   (* let a = Int.elt 2 in *)
   (* Format.printf "%d %d@." (Int.value a) (Int.value b); *)
   (* Int.union b a; *)
   Format.printf "%a@." pp_typ t3 *)

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
      if compare_typ t' t1' <> 0 then
        failwith
          (Format.asprintf "%s already has type %s but was used as type %s" v
             (string_of_type t1) (string_of_type t)))
    else TEnv.equate env.equalities t1 t;
    (* { env with eqs = (t, t1) :: env.eqs } *)
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
          (Format.asprintf "%s ~ %s"
             (string_of_type (TEnv.concretize env.equalities t1))
             (string_of_type (TEnv.concretize env.equalities t2))))
    else TEnv.equate env.equalities t1 t2;
    (* { env with eqs = (t1, t2) :: env.eqs } *)
    env)

(*
(* given a type variable and a substitution (a list of type equalities), finds the concrete type that the type variable is. not efficient. crashes (the entire program) on error *)
let find_concrete_type t bs =
  (* find all type variables in the same equivalence class *)
  let rec same_equiv_class ts ok =
    match ts with
    | [] -> ok
    | t :: ts1 ->
      let equiv =
        List.filter_map
          (fun (a, b) ->
            if a = t then Some b else if b = t then Some a else None)
          bs
        |> List.filter (fun a -> not (List.mem a ok))
      in
      same_equiv_class (ts1 @ equiv) (t :: ok)
  in
  (* check to ensure there is exactly one concrete type *)
  let conc =
    same_equiv_class [t] []
    |> List.filter (function TVar _ -> false | _ -> true)
    |> List.sort_uniq compare
  in
  match conc with
  | [t1] -> t1
  | [] when false ->
    failwith
      (Format.asprintf "failed to infer type for %s; bindings %s"
         (string_of_type t)
         (string_of_list (string_of_pair string_of_type string_of_type) bs))
  | [] ->
    (* default to int if there is insufficient information to infer. this is okay because it usually means there aren't any constraints on the variable, so one type is as good as any *)
    Int
  | _ :: _ ->
    failwith
      (Format.asprintf "type error: %s is used as all of: %s" (string_of_type t)
         (string_of_list string_of_type conc))
*)

let find_concrete_type = TEnv.concretize

let concrete_type_env abs : typ_env =
  (* abs.vartypes *)
  (* let all_bindings = abs.vartypes in *)
  (* Format.printf "all bindings %d %s@." (List.length all_bindings)
     (string_of_list (string_of_pair string_of_type string_of_type) all_bindings); *)
  (* figure out the concrete type for each program variable whose type is a type var *)
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
  | _ -> failwith (Format.asprintf "unknown function: %s" f)

let rec infer_types_term ?hint (env : abs_typ_env) term : typ * abs_typ_env =
  let res =
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
    | Plus (a, b), _ | Minus (a, b), _ ->
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
          (List.map2 (fun a b -> (a, b)) args argtypes)
      in
      (ret, env)
    | TList _, _ | TTupple _, _ -> failwith "list/tuple unimplemented"
  in
  debug ~at:5 ~title:"infer_types" "%s : %s -| %s" (string_of_term term)
    (string_of_type (fst res))
    (string_of_abs_env (snd res));
  res

let rec infer_types_pi env pi =
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
  | Predicate (_, _) -> failwith "not implemented"
