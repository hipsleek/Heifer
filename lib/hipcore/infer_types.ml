open Hiptypes
open Typedhip
open Pretty_typed
open Debug

let fresh_type_var () = TVar (ident_of_binder (verifier_getAfreeVar "v"))

(* record the type (or constraints on) of a program variable in the environment *)
let assert_var_has_type v t env =
  match SMap.find_opt v env.vartypes with
  | None -> { env with vartypes = SMap.add v t env.vartypes }
  | Some t1 -> (* unify_types t t1 env (* this probably also works*) *)
    if
      TEnv.has_concrete_type env.equalities t
      && TEnv.has_concrete_type env.equalities t1
    then (
      let t' = TEnv.concretize env.equalities t |> Option.get in
      let t1' = TEnv.concretize env.equalities t1 |> Option.get in
      match t1 with       (* ASK Darius *)
      | TVar _ -> ()      (* ASK Darius *)
      | _ ->              (* ASK Darius *)
      if compare_typ t' t1' <> 0 then
        failwith
          (Format.asprintf "%s already has type %s but was used as type %s" v
             (string_of_type t1) (string_of_type t)))
    else TEnv.equate env.equalities t1 t;
    env

(** Exception raised when solver cannot unify the two types. *)
exception Unification_failure of typ * typ

(** [Cyclic_type t1 t2] is raised when, during type unification, t1's value
    is found to rely on t2. *)
exception Cyclic_type of typ * typ

let () =
  Printexc.register_printer begin function
    | Unification_failure (t1, t2) -> Some (Printf.sprintf "Unification_failure(%s, %s)" (string_of_type t1) (string_of_type t2))
    | Cyclic_type (t1, t2) -> Some (Printf.sprintf "Cyclic_type(%s, %s)" (string_of_type t1) (string_of_type t2))
    | _ -> None
  end

(* record a (nontrivial) equality in the environment *)
let rec unify_types t1 t2 env =
  debug ~at:5 ~title:"unify" "%s ~ %s" (string_of_type t1) (string_of_type t2);
  match TEnv.(simplify env.equalities t1, simplify env.equalities t2) with
  (* case where one of t1, t2 is a type variable: *)
  | TVar _ as var, simp | simp, (TVar _ as var) -> 
      TEnv.equate env.equalities var simp;
      (* check for cycles in the equality map *)
      let var_simplified = TEnv.simplify env.equalities var in
      if (compare_typ var var_simplified <> 0) && List.mem var (type_vars_used var_simplified)
      then raise (Cyclic_type (var, var_simplified))
      else env
  (* case where t1 and t2 are both type constructors: *)
  | TConstr (name1, args1) as simp_t1, (TConstr (name2, args2) as simp_t2) -> 
      if name1 = name2
      then List.fold_left2 (fun env p1 p2 -> unify_types p1 p2 env) env args1 args2
      else raise (Unification_failure (simp_t1, simp_t2))
  (* case where t1 and t2 are the same type: *)
  | t1, t2 when compare_typ t1 t2 = 0 -> env
  (* as of now, unification is not possible in all other cases *)
  | t1, t2 -> raise (Unification_failure (t1, t2))

let find_concrete_type = TEnv.concretize

let concrete_type_env abs : typ_env =
  let simpl t = 
    TEnv.simplify abs.equalities t in
  SMap.map simpl abs.vartypes

let get_primitive_type f =
  let untype = Typedhip.Untypehip.hiptypes_typ in
  let list_int = TConstr ("list", [Int]) in
  match f with
  | "cons" -> ([Int; ], list_int)
  | "head" -> ([list_int], Int)
  | "tail" -> ([list_int], list_int)
  | "is_nil" | "is_cons" -> ([list_int], Bool)
  | "+" | "-" -> ([Int; Int], Int)
  | "string_of_int" -> ([Int], TyString)
  | _ when String.compare f "effNo" == 0 -> ([Int] , Int)
  | _ when Globals.is_pure_fn_defined f ->
    let fn = Globals.pure_fn f in
    (List.map snd fn.pf_params |> List.map untype, fn.pf_ret_type |> untype)
  | _ when SMap.mem f Globals.global_environment.pure_fn_types ->
    let fn = SMap.find f Globals.global_environment.pure_fn_types in
    (fn.pft_params |> List.map untype, fn.pft_ret_type |> untype)
  | _ ->
      failwith (Format.asprintf "unknown function 2: %s" f)

let get_primitive_fn_type f =
  match f with
  | "=" -> ([Int; Int], Bool)
  | _ -> failwith (Format.asprintf "unknown function: %s" f)

(** Given a function to infer the types of elements of a list,
infer types in the list, threading the environment through. *)
let infer_types_list f env ls =
    List.fold_right (fun t (acc, env) ->
      let t, env = f env t in
      (t::acc, env)) ls ([], env)

let rec infer_types_core_lang env e : core_lang * abs_typ_env =
  match e.core_desc with
  | CValue t -> 
      let term, env = infer_types_term env t in
      {core_desc = CValue term; core_type = term.term_type}, env
  | CFunCall (f, args) ->
    let ex_args, ex_ret = get_primitive_fn_type f in
    let args, env =
    List.fold_right2 (fun arg ex_arg (t, env) ->
      let inf_arg, env = infer_types_term env arg in
      let env = unify_types inf_arg.term_type ex_arg env in
      inf_arg :: t, env
      ) args ex_args ([], env)
    in
    {core_desc = CFunCall (f, args); core_type = ex_ret}, env
  | CLet (x, e1, e2) ->
    let t1, env = infer_types_core_lang env e1 in
    (* let-polymorphism would be nice to have here *)
    let env = assert_var_has_type x t1.core_type env in
    let t2, env = infer_types_core_lang env e2 in
    {core_desc = CLet (x, t1, t2); core_type = t2.core_type}, env
  | CIfElse (cond, if_, else_) ->
      let cond, env = infer_types_pi env cond in
      let if_, env = infer_types_core_lang env if_ in
      let else_, env = infer_types_core_lang env else_ in
      let env = unify_types if_.core_type else_.core_type env in
      {core_desc = CIfElse (cond, if_, else_); core_type = if_.core_type}, env
  | CWrite (loc, v) ->
      let v, env = infer_types_term env v in
      {core_desc = CWrite (loc, v); core_type = Unit}, env
  | CRef v ->
      let v, env = infer_types_term env v in
      {core_desc = CRef v; core_type = TConstr ("ref", [v.term_type])}, env
  | CRead loc ->
      let result_type = fresh_type_var () in
      (* assert the equality so we can also typecheck the uses *)
      let env = assert_var_has_type loc result_type env in
      {core_desc = CRead loc; core_type = result_type}, env
  | CMatch (_, _, _, _, _) -> failwith "CMatch"
  | CPerform (_, _) -> failwith "CPerform"
  | CAssert (_, _) -> failwith "CAssert"
  | CResume _ -> failwith "CResume"
  | CShift (_, _, _) | CReset _
  | CLambda (_, _, _) ->
    failwith "not implemented"

and infer_types_term ?hint (env : abs_typ_env) term : term * abs_typ_env =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:5 ~title:"infer_types" "%s : %s -| %s" (string_of_term term)
          (string_of_result string_of_type (map_presult (fun (t, _) -> t.term_type) r))
          (string_of_result string_of_abs_env (map_presult snd r)))
  in
  let term, env = match (term.term_desc, hint) with
  | Const c, _ -> let term_type = match c with
    | TStr _ -> TyString
    | TTrue | TFalse -> Bool
    | ValUnit -> Unit
    | Num _ -> Int
    | Nil -> begin match hint with 
        | Some ((TConstr ("list", [_])) as list_type) -> list_type
        | _ -> TConstr ("list", [fresh_type_var ()])
      end
    in ({term_desc = Const c; term_type}, env)
  | TNot a, _ ->
    let a, env1 = infer_types_term ~hint:Bool env a in
    ({term_desc = TNot a; term_type = Bool}, env1)
  | BinOp (op, a, b), _ ->
    let a_hint, b_hint, term_type = match op with
      | TOr | TAnd -> Bool, Bool, Bool
      | TCons -> 
          let element_type = fresh_type_var () in
          element_type, TConstr ("list", [element_type]), TConstr ("list", [element_type])
      | Plus | Minus | TTimes | TDiv | TPower -> Int, Int, Int
      | SConcat -> TyString, TyString, TyString
    in
    let a, env = infer_types_term ~hint:a_hint env a in
    let b, env = infer_types_term ~hint:b_hint env b in
    ({term_desc = BinOp(op, a, b); term_type}, env)
  (* possibly add syntactic heuristics for types, such as names *)
  | Var v, Some t -> ({term_desc = Var v; term_type = t}, assert_var_has_type v t env)
  | Var v, None ->
    let t = TVar (ident_of_binder (verifier_getAfreeVar v)) in
    ({term with term_type = t}, assert_var_has_type v t env)
  | TLambda (_, _, _, Some _), _
  | TLambda (_, _, _, None), _ -> ({term with term_type = Lamb}, env)
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
      let a, env1 = infer_types_term ?hint env a in
      let b, env2 = infer_types_term ?hint env1 b in
      let env3 = unify_types a.term_type b.term_type env2 in
      {term_desc = Rel(EQ, a, b); term_type = Bool}, env3
  end
  | Rel ((GT | LT | GTEQ | LTEQ), a, b), _ ->
    let a, env1 = infer_types_term ~hint:Int env a in
    let b, env2 = infer_types_term ~hint:Int env1 b in
    {term_desc = Rel(EQ, a, b); term_type = Bool}, env2
  | TApp (f, args), _ ->
    let argtypes, ret = get_primitive_type f in
    let args, env =
      List.map2 pair args argtypes |>
        (* infer from right to left *)
        List.fold_left
          (fun (typed_args, env) (a, at) ->
            let typed_arg, env = infer_types_term ~hint:at env a in
            typed_args @ [typed_arg], env)
          ([], env)
    in
    {term_desc = TApp(f, args); term_type = ret}, env
  | Construct (name, args), _ ->
      let type_decl, (constr_params, constr_arg_types) = Globals.type_constructor_decl name in
      let concrete_bindings = List.map (fun param -> (param, fresh_type_var ())) constr_params in
      let concrete_vars = List.map (fun (_, var) -> var) concrete_bindings in
      let args, env = List.map2 pair args constr_arg_types
      |> List.fold_left
      (fun (typed_args, env) (arg, arg_type) ->
        let expected_arg_type = Types.instantiate_type_variables concrete_bindings arg_type in
        let typed_arg, env = infer_types_term ~hint:expected_arg_type env arg in
        typed_args @ [typed_arg], env) ([], env) in
      {term_desc = Construct (name, args); term_type = TConstr (type_decl.typ_name, concrete_vars)}, env
  | TList _, _ | TTuple _, _ -> failwith "constructor/list/tuple unimplemented"
  in
  (* After checking this term, we may still need to unify its type with a hint received from above in the AST. *)
  let term, env = match hint with
  | Some typ -> term, unify_types typ term.term_type env
  | None -> term, env
  in
  (* Update the variable type mapping with any unifications done so far. This is repetitive;
     it's probably better to store typ U.elems in the mapping instead. *)
  term, { env with vartypes = SMap.map (TEnv.simplify env.equalities) env.vartypes }

and infer_types_kappa env k = match k with
  | EmptyHeap -> EmptyHeap, env
  | SepConj (k1, k2) ->
      let k1, env = infer_types_kappa env k1 in
      let k2, env = infer_types_kappa env k2 in
      SepConj(k1, k2), env
  | PointsTo(l, v) ->
    let term_type = fresh_type_var () in
    let v, env = infer_types_term env v ~hint:term_type in
    PointsTo(l, v), env


(** Given an environment, and a typed term, perform simplifications
    on the types in the term based on the environment. *)
and simplify_types_pi env pi =
  let go = object (self)
    inherit [_] map_spec

    method! visit_term env term =
      let result = {term_desc = self#visit_term_desc env term.term_desc;
      term_type = 
        TEnv.simplify env.equalities term.term_type} in
      debug ~at:5 ~title:"inference result" "%s : %s\n" (string_of_term result) (string_of_type result.term_type);
      result
  end in
  go#visit_pi env pi

(* Given a typed pure formula, fill in the needed missing type information. *)
and infer_types_pi env pi : pi * abs_typ_env =
  (* let@ _ =
       Debug.span (fun r ->
           debug ~at:5 ~title:"infer_types_pi" "%s -| %s" (string_of_pi pi)
             (string_of_result string_of_abs_env r))
     in *)
  match pi with
  | True | False -> pi, env
  | Atomic (EQ, a, b) ->
    let t1, env = infer_types_term env a in
    let t2, env = infer_types_term env b in
    (* Format.printf "EQ %s = %s@." (string_of_term a) (string_of_term b); *)
    let env = unify_types t1.term_type t2.term_type env in
    Atomic(EQ, t1, t2), env
  | Atomic (GT as op, a, b)
  | Atomic (LT as op, a, b)
  | Atomic (GTEQ as op, a, b)
  | Atomic (LTEQ as op, a, b) -> begin
    let t1, env = infer_types_term ~hint:Int env a in
    let t2, env = infer_types_term ~hint:Int env b in
    Atomic(op, t1, t2), env
  end
  | And (a, b) ->
    let t1, env = infer_types_pi env a in
    let t2, env = infer_types_pi env b in
    And (t1, t2), env
  | Or (a, b) -> 
    let t1, env = infer_types_pi env a in
    let t2, env = infer_types_pi env b in
    Or (t1, t2), env
  | Imply (a, b) ->
    let t1, env = infer_types_pi env a in
    let t2, env = infer_types_pi env b in
    Imply (t1, t2), env
  | Not a -> 
      let t, env = infer_types_pi env a in
      Not t, env
  | Predicate (_, _) -> pi, env
  | Subsumption (_, _) -> pi, env

and infer_types_staged_spec env spec =
  match spec with
  | Require (pi, kappa) ->
    let pi, env = infer_types_pi env pi in
    let kappa, env = infer_types_kappa env kappa in
    Require(pi, kappa), env
  | NormalReturn (pi, kappa) ->
    let pi, env = infer_types_pi env pi in
    let kappa, env = infer_types_kappa env kappa in
    NormalReturn(pi, kappa), env
  | HigherOrder (pi, kappa, (name, args), term) ->
    let pi, env = infer_types_pi env pi in
    let kappa, env = infer_types_kappa env kappa in
    let args, env = List.fold_right (fun t (acc, env) ->
      let t, env = infer_types_term env t in
      (t::acc, env)) args ([], env) in
    let term, env = infer_types_term env term in
    HigherOrder(pi, kappa, (name, args), term), env
  | RaisingEff (pi, kappa, (name, args), term) -> 
    let pi, env = infer_types_pi env pi in
    let kappa, env = infer_types_kappa env kappa in
    let args, env = infer_types_list infer_types_term env args in
    let term, env = infer_types_term env term in
    RaisingEff (pi, kappa, (name, args), term), env
  | TryCatch (pi, kappa, trycatch, term) ->
    let pi, env = infer_types_pi env pi in
    let kappa, env = infer_types_kappa env kappa in
    let trycatch, env = 
      let (spec, (var_case, eff_specs)) = trycatch in
      let spec, env = infer_types_spec env spec in
      let var_case, env =
        let (var_name, var_spec) = var_case in
        let env = assert_var_has_type var_name (fresh_type_var ()) env in
        let var_spec, env = infer_types_disj_spec env var_spec in
        (var_name, var_spec), env
      in
      let infer_eff_case env eff =
        let (eff_name, eff_arg, eff_spec) = eff in
        let env = match eff_arg with
          | Some arg -> assert_var_has_type arg (fresh_type_var ()) env
          | None -> env
        in
        let eff_spec, env = infer_types_disj_spec env eff_spec in
        (eff_name, eff_arg, eff_spec), env
      in
      let eff_specs, env = infer_types_list infer_eff_case env eff_specs in
      (spec, (var_case, eff_specs)), env
    in 
    let term, env = infer_types_term env term in
    TryCatch(pi, kappa, trycatch, term), env
  (* skip on typing shift/reset specs for now *)
  | Shift (kind, k, spec, term)  -> Shift (kind, k, spec, term), env
  | Reset (spec, term) -> Reset (spec, term), env
  | _ -> failwith "todo"

and infer_types_spec env spec = infer_types_list infer_types_staged_spec env spec

and infer_types_disj_spec env spec = infer_types_list infer_types_spec env spec


let infer_types_pi env pi =
  (* shadow the previous declaration so we can run one last simplification pass over the types *)
  let pi, env = infer_types_pi env pi in (* referring to the previous declaration *)
  simplify_types_pi env pi, env

(** Given an untyped term, fill it with type information. *)
let infer_untyped_pi ?(env = create_abs_env ()) pi =
  infer_types_pi env (Fill_type.fill_untyped_pi pi)

(** Output a list of types after being unified in some environment. Mainly
    used for testing. *)
let output_simplified_types env ts =
  ts |> List.iteri (fun i t ->
    Printf.printf "t%d: %s\n" i (string_of_type (TEnv.simplify env.equalities t)))

let%expect_test "unification with type constructors" =
  let env = create_abs_env () in
  let t1 = TConstr ("list", [TVar "a"]) in
  let t2 = TConstr ("list", [TVar "c"]) in
  let t3 = TVar "c" in
  let t4 = TConstr ("list", [Int]) in
  let env = unify_types t1 t2 env in
  let env = unify_types t3 t4 env in
  output_simplified_types env [t1; t2; t3; t4];
  [%expect {|
    t0: int list list
    t1: int list list
    t2: int list
    t3: int list
    |}]

let%expect_test "unification" =
  let env = create_abs_env () in
  let t1 = TVar "a" in
  let t2 = TVar "b" in
  let t3 = TVar "c" in
  let t4 = TConstr ("list", [Int]) in
  let t5 = Unit in
  let env = unify_types t1 t2 env in
  let env = unify_types t1 t4 env in
  let env = unify_types t5 t3 env in
  output_simplified_types env [t1; t2; t3; t4; t5];
  [%expect {|
    t0: int list
    t1: int list
    t2: unit
    t3: int list
    t4: unit
    |}]

let%expect_test "unsolvable unification: cyclic solution" =
  Printexc.record_backtrace false;
  let env = create_abs_env () in
  let t1 = TConstr ("list", [TConstr ("list", [TVar "a"])]) in
  let t2 = TConstr ("list", [TVar "a"]) in
  let _ = unify_types t1 t2 env in
  output_simplified_types env [t1; t2];
  [@@expect.uncaught_exn {| ("Cyclic_type('a, 'a list list)") |}]

let%expect_test "unsolvable unification: incompatible types" =
  Printexc.record_backtrace false;
  let env = create_abs_env () in
  let t1 = Int in
  let t2 = Bool in
  let _ = unify_types t1 t2 env in
  output_simplified_types env [t1; t2];
  [@@expect.uncaught_exn {| ("Unification_failure(int, bool)") |}]

let%expect_test "term inference" =
  let env = create_abs_env () in
  let p1 = Hiptypes.(And (Atomic(GT, Var "a", Var "b"), Atomic(EQ, Var "c", Construct ("::", [Var "b"; Nil])))) in
  let p1_typed, _ = infer_untyped_pi p1 ~env in
  begin match p1_typed with
  | And (Atomic(GT, {term_type = a_type; _}, {term_type = b_type; _}),
    Atomic(EQ, {term_type = c_type; _}, {term_type = ls_type; term_desc = Construct ("::", [_; {term_type = nil_type; _}])})) ->
      Printf.printf "types: (%s) (%s) (%s) (%s) (%s)\n" (string_of_type a_type) (string_of_type b_type) (string_of_type c_type)
      (string_of_type ls_type) (string_of_type nil_type)
  | _ -> Printf.printf "INVALID"
  end;
  [%expect {|
    types: (int) (int) (int list) (int list) (int list)
    |}]

let%expect_test "term inference 2" =
  let env = create_abs_env () in
  let p1 = Hiptypes.(And (Atomic(EQ, Var "a", Plus (Var "b", Num 1)), Atomic(EQ, Var "c", Construct ("::", [Var "a"; Var "d"])))) in
  let p1_typed, _ = infer_untyped_pi p1 ~env in
  begin match p1_typed with
  | And (Atomic(EQ, {term_type = a_type; _}, {term_desc = BinOp(Plus, {term_type = b_type; _}, _); _}),
    Atomic(EQ, {term_type = c_type; _}, {term_type = ls_type; term_desc = Construct("::", [_; {term_type = d_type; _}])})) ->
      Printf.printf "types: (%s) (%s) (%s) (%s) (%s)\n" (string_of_type a_type) (string_of_type b_type) (string_of_type c_type)
      (string_of_type ls_type) (string_of_type d_type)
  | _ -> Printf.printf "INVALID"
  end;
  [%expect {| types: (int) (int) (int list) (int list) (int list) |}]
