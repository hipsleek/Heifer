open Hipcore
open Hipcore.Common
open Hipcore.Types
open Hipcore_typed.Typedhip
open Hipcore_typed.Pretty
open Debug
open Utils

let fresh_type_var () = TVar (Variables.fresh_variable ())

type 'a using_env = ('a, abs_typ_env) State.state
let span_env = State.Debug.span
let return = State.return
let (let*) = State.(let*)

(** Run a type inference computation with an empty initial environment. *)
let with_empty_env f = f (create_abs_env ())

(** Add the following variable bindings to the inference environment. *)
let add_vartypes vars env =
  let f _ v1 _ = Some v1 in
  (), { env with vartypes = Common.SMap.union f (SMap.of_seq vars) env.vartypes }

(** Run a type inference computation with some added bindings.
    The bindings are removed at the end. *)
let with_vartypes vars f =
  State.scope begin
    let* _ = add_vartypes vars in
    f
  end
  

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
let rec unify_types t1 t2 : unit using_env =
  fun env ->
    debug ~at:5 ~title:"unify" "%s ~ %s" (string_of_type t1) (string_of_type t2);
    match TEnv.(simplify env.equalities t1, simplify env.equalities t2) with
    (* case where one of t1, t2 is a type variable: *)
    | TVar var_name as var, simp | simp, (TVar var_name as var) -> 
        TEnv.equate env.equalities var simp;
        (* check for cycles in the equality map *)
        let var_simplified = TEnv.simplify env.equalities var in
        if (compare_typ var var_simplified <> 0) && List.mem var_name (free_type_vars var_simplified)
        then raise (Cyclic_type (var, var_simplified))
        else (), env
    (* case where t1 and t2 are both type constructors: *)
    | TConstr (name1, args1) as simp_t1, (TConstr (name2, args2) as simp_t2) -> 
        if name1 = name2
        then (), List.fold_left2 (fun env p1 p2 -> unify_types p1 p2 env |> snd) env args1 args2
        else raise (Unification_failure (simp_t1, simp_t2))
    (* case where t1 and t2 are the same type: *)
    | t1, t2 when compare_typ t1 t2 = 0 -> (), env
    (* case where one of the types is Any *)
    | Any, _ | _, Any -> (), env
    (* as of now, unification is not possible in all other cases *)
    | t1, t2 -> raise (Unification_failure (t1, t2))

(* record the type (or constraints on) of a program variable in the environment *)
let assert_var_has_type (v, v_typ : binder) t env =
  let (), env = unify_types v_typ t env in begin
  match SMap.find_opt v env.vartypes with
  | None -> (), { env with vartypes = SMap.add v t env.vartypes }
  | Some t1 -> (* unify_types t t1 env (* this probably also works*) *)
    begin
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
             (string_of_type t1') (string_of_type t')))
    else let (), _ = unify_types t1 t env in ()
    end;
    (), env
  end


let find_concrete_type = TEnv.concretize

let concrete_type_env abs : typ_env =
  let simpl t = 
    TEnv.simplify abs.equalities t in
  SMap.map simpl abs.vartypes

let get_primitive_type f =
  let open Hipcore_typed.Globals in
  (* let untype = Typedhip.Untypehip.hiptypes_typ in *)
  let v = fresh_type_var () in
  let list_of_v = TConstr ("list", [v]) in
  match f with
  | "cons" -> ([v; list_of_v], list_of_v)
  | "head" -> ([list_of_v], v)
  | "tail" -> ([list_of_v], list_of_v)
  | "is_nil" | "is_cons" -> ([list_of_v], Bool)
  | "+" | "-" -> ([Int; Int], Int)
  | "string_of_int" -> ([Int], TyString)
  | _ when String.compare f "effNo" == 0 -> ([Int] , Int)
  | _ when is_pure_fn_defined f ->
    let fn = pure_fn f in
    (List.map snd fn.pf_params, fn.pf_ret_type)
  | _ when SMap.mem f global_environment.pure_fn_types ->
    let fn = SMap.find f global_environment.pure_fn_types in
    (fn.pft_params, fn.pft_ret_type)
  | _ ->
      failwith (Format.asprintf "unknown function 2: %s" f)

let get_primitive_fn_type f =
  match f with
  | "=" -> ([Int; Int], Bool)
  | _ -> failwith (Format.asprintf "unknown function: %s" f)

let wrap_as_ref t = TConstr ("ref", [t])

let rec infer_types_core_lang e : core_lang using_env =
  let* core_desc, core_type = match e.core_desc with
  | CValue t -> 
      let* t = infer_types_term t in
      return (CValue t, t.term_type)
  | CFunCall (f, args) ->
    let arg_types, ret_type = get_primitive_fn_type f in
    (* TODO check for length mismatch? *)
    let* args =
      List.combine args arg_types
      |> State.map ~f:(fun (arg, expected_type) ->
          let* inferred_term = infer_types_term arg in
          let* _ = unify_types inferred_term.term_type expected_type in
          return inferred_term)
    in
    return (CFunCall (f, args), ret_type)
  | CLet (x, e1, e2) ->
    let* e1 = infer_types_core_lang e1 in
    let* _ = assert_var_has_type x e1.core_type in
    let* e2 = infer_types_core_lang e2 in
    return (CLet (x, e1, e2), e2.core_type)
  | CSequence (e1, e2) ->
    let* e1 = infer_types_core_lang e1 in
    let* e2 = infer_types_core_lang e2 in
    (* TODO should this be added? *)
    (* let* _ = unify_types e1.core_type Unit in *)
    return (CSequence (e1, e2), e2.core_type)
  | CIfElse (cond, if_true, if_false) ->
      let* cond = infer_types_pi cond in
      let* if_true = infer_types_core_lang if_true in
      let* if_false = infer_types_core_lang if_false in
      let* _ = unify_types if_true.core_type if_false.core_type in
      return (CIfElse (cond, if_true, if_false), if_true.core_type)
  | CWrite (loc, value) ->
      let* value = infer_types_term value in
      let loc_type = wrap_as_ref value.term_type in
      let* _ = assert_var_has_type (loc, loc_type) loc_type in
      return (CWrite (loc, value), Unit)
  | CRef value ->
      let* value = infer_types_term value in
      return (CRef value, wrap_as_ref value.term_type)
  | CRead value ->
      let val_type = fresh_type_var () in
      let* _ = assert_var_has_type (value, wrap_as_ref val_type) (wrap_as_ref val_type) in
      return (CRead value, val_type)
  | CAssert (_, _) -> failwith "CAssert"
  | CPerform (_, _) -> failwith "CPerform"
  | CMatch (_, _, _, _, _) -> failwith "CMatch"
  | CResume _ -> failwith "CResume"
  | CShift (_, _, _) | CReset _
  | CLambda (_, _, _) ->
    failwith "not implemented"
  in
  return {core_desc; core_type}

and infer_types_term ?(hint : typ option) term : term using_env =
  let@ _ =
    span_env (fun r ->
        debug ~at:5 ~title:"infer_types" "%s : %s -| %s" (string_of_term term)
          (string_of_result string_of_term (State.Debug.presult_value r))
          (string_of_result string_of_abs_env (State.Debug.presult_state r)))
  in
  let* (term_desc, term_type) = match (term.term_desc, hint) with
  | Const c, hint ->
      let term_type = match c with
      | ValUnit -> Unit
      | TTrue | TFalse -> Bool
      | TStr _ -> TyString
      | Num _ -> Int
      | Nil -> begin match hint with 
        | Some ((TConstr ("list", [_])) as list_type) -> list_type
        | _ -> TConstr ("list", [fresh_type_var ()])
      end
      in
      return (term.term_desc, term_type)
  | TNot a, _ ->
    let* a = infer_types_term ~hint:Bool a in
    return (TNot a, Bool)
  | BinOp (op, a, b), _ ->
      let atype, btype, ret_type = match op with
        | TCons ->
            let element_type = fresh_type_var () in
            element_type, TConstr ("list", [element_type]), TConstr ("list", [element_type])
        | TAnd| TOr -> Bool, Bool, Bool
        | SConcat -> TyString, TyString, TyString
        | Plus | Minus | TTimes | TDiv | TPower -> Int, Int, Int
      in
      let* a = infer_types_term ~hint:atype a in
      let* b = infer_types_term ~hint:btype b in
      return (BinOp (op, a, b), ret_type)
  (* possibly add syntactic heuristics for types, such as names *)
  | Var v, Some t -> 
      let* _ = assert_var_has_type (v, term.term_type) t in
      return (term.term_desc, t)
  | Var v, None ->
    let t = (TVar (Variables.fresh_variable v)) in
    let* _ = assert_var_has_type (v, term.term_type) t in
    return (term.term_desc, t)
  | TLambda (_, _, _, Some _), _
  | TLambda (_, _, _, None), _ -> return (term.term_desc, Lamb)
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
  | Rel (EQ, a, b), _ ->
    let* a = infer_types_term a in
    let* b = infer_types_term b in
    let* _ = unify_types a.term_type b.term_type in
    return (Rel (EQ, a, b), Bool)
  | Rel ((GT | LT | GTEQ | LTEQ as op), a, b), _ ->
    let* a = infer_types_term ~hint:Int a in
    let* b = infer_types_term ~hint:Int b in
    return (Rel (op, a, b), Bool)
  | TApp (f, args), _ ->
    let arg_types, ret_type = get_primitive_type f in
    let* args =
      List.combine args arg_types
      |> State.map ~f:(fun (arg, expected_type) ->
          let* arg = infer_types_term arg in
          let* _ = unify_types arg.term_type expected_type in
          return arg)
    in
    return (TApp (f, args), ret_type)
  | Construct (name, args), _ ->
      let type_decl, (constr_params, constr_arg_types) = Hipcore_typed.Globals.type_constructor_decl name in
      let concrete_bindings = List.map (fun param -> (param, fresh_type_var ())) constr_params in
      let concrete_vars = List.map (fun (_, var) -> var) concrete_bindings in
      (* let args, env = List.map2 pair args constr_arg_types *)
      (* |> List.fold_left *)
      (* (fun (typed_args, env) (arg, arg_type) -> *)
      (*   let expected_arg_type = Types.instantiate_type_variables concrete_bindings arg_type in *)
      (*   let typed_arg, env = infer_types_term ~hint:expected_arg_type env arg in *)
      (*   typed_args @ [typed_arg], env) ([], env) in *)
      let* args = List.combine args constr_arg_types
        |> State.map ~f:(fun (arg, arg_type) ->
          let expected_arg_type = Types.instantiate_type_variables concrete_bindings arg_type in
          infer_types_term ~hint:expected_arg_type arg) in
      return (Construct (name, args), TConstr (type_decl.tdecl_name, concrete_vars))
  | TTuple _, _ -> failwith "tuple unimplemented"
  in
  (* After checking this term, we may still need to unify its type with a hint received from above in the AST. *)
  let* _ = match hint with
  | Some typ -> unify_types term_type typ
  | None -> return ()
  in
  (* Update the variable type mapping with any unifications done so far. This is repetitive;
     it's probably better to store typ U.elems in the mapping instead. *)
  let* _ = State.mutate simplify_vartypes in
  return {term_desc; term_type}

and infer_types_pi pi : pi using_env =
  let@ _ =
       span_env (fun r ->
           debug ~at:5 ~title:"infer_types_pi" "%s -| %s" (string_of_pi pi)
             (string_of_result string_of_abs_env (State.Debug.presult_state r)))
     in
  match pi with
  | True | False -> return pi
  | Atomic (EQ, a, b) ->
    let* a = infer_types_term a in
    let* b = infer_types_term b in
    let* _ = unify_types a.term_type b.term_type in
    return (Atomic (EQ, a, b))
  | Atomic (GT | LT | GTEQ | LTEQ as op, a, b) ->
    let hint = Int in
    let* a = infer_types_term a ~hint in
    let* b = infer_types_term b ~hint in
    return (Atomic (op, a, b))
  | And (a, b) ->
    let* a = infer_types_pi a in
    let* b = infer_types_pi b in
    return (And (a, b))
  | Or (a, b) ->
    let* a = infer_types_pi a in
    let* b = infer_types_pi b in
    return (Or (a, b))
  | Imply (a, b) ->
    let* a = infer_types_pi a in
    let* b = infer_types_pi b in
    return (Imply (a, b))
  | Not a -> 
      let* _ = infer_types_pi a in
      return (Not a)
  | pi -> return pi

(* re-declare to insert one final type simplification pass *)

let simplify_type_visitor = object (self)
  (* go over all types in the AST and simplify them. *)
  inherit [_] map_spec
  (* the main ones *)
  method! visit_term env term =
    let result = {term_desc = self#visit_term_desc env term.term_desc;
    term_type = 
      TEnv.simplify env.equalities term.term_type} in
    debug ~at:5 ~title:"inference result" "%s : %s\n" (string_of_term result) (string_of_type result.term_type);
    result

  method! visit_core_lang env core =
    {core_desc = self#visit_core_lang_desc env core.core_desc; core_type = TEnv.simplify env.equalities core.core_type}

  method! visit_pattern env pat =
    {pattern_desc = self#visit_pattern_desc env pat.pattern_desc; pattern_type = TEnv.simplify env.equalities pat.pattern_type}

  method! visit_binder env b =
    (ident_of_binder b, TEnv.simplify env.equalities (type_of_binder b))

end

(** Given an environment, and a typed term, perform simplifications
    on the types in the term based on the environment. *)
let simplify_types_pi pi env =
  simplify_type_visitor#visit_pi env pi, env

let simplify_types_staged_spec ss env =
  simplify_type_visitor#visit_staged_spec env ss, env

let infer_types_term ?hint t : term using_env =
  let* t = infer_types_term ?hint t in
  let* env = State.get in
  return (simplify_type_visitor#visit_term env t)

let simplify_types_core_lang core env =
  simplify_type_visitor#visit_core_lang env core, env

let infer_types_pi pi : pi using_env =
  let* pi = infer_types_pi pi in
  simplify_types_pi pi

let infer_types_pair_pi (p1, p2) : (pi * pi) using_env =
  let* p1 = infer_types_pi p1 in
  let* p2 = infer_types_pi p2 in
  (* we may have found new unifications while inferring p2, so simplify p1 *)
  let* p1 = simplify_types_pi p1 in
  return (p1, p2)


let rec infer_types_kappa k : kappa using_env =
  match k with
  | EmptyHeap -> return EmptyHeap
  | SepConj (k1, k2) ->
      let* k1 = infer_types_kappa k1 in
      let* k2 = infer_types_kappa k2 in
      return (SepConj (k1, k2))
  | PointsTo(l, v) ->
    let* v = infer_types_term v in
    let ref_type = wrap_as_ref v.term_type in
    let* _ = assert_var_has_type (l, ref_type) ref_type in
    return (PointsTo (l, v))

let rec infer_types_state (p, k) : state using_env =
  let* p = infer_types_pi p in
  let* k = infer_types_kappa k in
  return (p, k)

let rec infer_types_staged_spec ss : staged_spec using_env =
  let* typed_spec = match ss with
  | Require (p, k) ->
      let* (p, k) = infer_types_state (p, k) in
      return (Require (p, k))
  | NormalReturn (p, k) ->
      let* (p, k) = infer_types_state (p, k) in
      return (NormalReturn (p, k))
  | HigherOrder (f, args) ->
      let* args = State.map ~f:infer_types_term args in
      return (HigherOrder (f, args))
  | Shift (b, k, spec, x, cont) ->
      let* spec = infer_types_staged_spec spec in
      let* cont = infer_types_staged_spec cont in
      return (Shift (b, k, spec, x, cont))
  | Reset spec ->
      let* spec = infer_types_staged_spec spec in
      return (Reset spec)
  | Sequence (s1, s2) ->
      let* s1 = infer_types_staged_spec s1 in
      let* s2 = infer_types_staged_spec s2 in
      return (Sequence (s1, s2))
  | Bind (f, s1, s2) ->
      let* s1 = infer_types_staged_spec s1 in
      let* s2 = infer_types_staged_spec s2 in
      return (Bind (f, s1, s2))
  | Disjunction (s1, s2) ->
      let* s1 = infer_types_staged_spec s1 in
      let* s2 = infer_types_staged_spec s2 in
      return (Disjunction (s1, s2))
  | Exists ((x, t), spec) ->
      with_vartypes (List.to_seq [x, t]) begin
        let* spec = infer_types_staged_spec spec in
        return (Exists ((x, t), spec))
      end
  | ForAll ((x, t), spec) ->
      with_vartypes (List.to_seq [x, t]) begin
        let* spec = infer_types_staged_spec spec in
        return (ForAll ((x, t), spec))
      end
  | RaisingEff _ | TryCatch _ -> failwith "infer_types_staged_spec: not implemented"
  in
  (* assert (Untypehip.untype_staged_spec typed_spec = Untypehip.untype_staged_spec ss); *)
  return typed_spec

let infer_types_staged_spec ss : staged_spec using_env =
  let* ss = infer_types_staged_spec ss in
  let* env = State.get in
  return (simplify_type_visitor#visit_staged_spec env ss)

let infer_types_pair_staged_spec p1 p2 : (staged_spec * staged_spec) using_env =
  let* p1 = infer_types_staged_spec p1 in
  let* p2 = infer_types_staged_spec p2 in
  (* we may have found new unifications while inferring p2, so simplify p1 *)
  let* p1 = simplify_types_staged_spec p1 in
  return (p1, p2)

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
  let _, env = unify_types t1 t2 env in
  let _, env = unify_types t3 t4 env in
  output_simplified_types env [t1; t2; t3; t4];
  [%expect {|
    t0: ((int) list) list
    t1: ((int) list) list
    t2: (int) list
    t3: (int) list
    |}]

let%expect_test "unification" =
  let env = create_abs_env () in
  let t1 = TVar "a" in
  let t2 = TVar "b" in
  let t3 = TVar "c" in
  let t4 = TConstr ("list", [Int]) in
  let t5 = Unit in
  let _, env = unify_types t1 t2 env in
  let _, env = unify_types t1 t4 env in
  let _, env = unify_types t5 t3 env in
  output_simplified_types env [t1; t2; t3; t4; t5];
  [%expect {|
    t0: (int) list
    t1: (int) list
    t2: unit
    t3: (int) list
    t4: unit
    |}]

let%expect_test "unsolvable unification: cyclic solution" =
  Printexc.record_backtrace false;
  let env = create_abs_env () in
  let t1 = TConstr ("list", [TConstr ("list", [TVar "a"])]) in
  let t2 = TConstr ("list", [TVar "a"]) in
  let _ = unify_types t1 t2 env in
  output_simplified_types env [t1; t2];
  [@@expect.uncaught_exn {| ("Cyclic_type('a, (('a) list) list)") |}]

let%expect_test "unsolvable unification: incompatible types" =
  Printexc.record_backtrace false;
  let env = create_abs_env () in
  let t1 = Int in
  let t2 = Bool in
  let _ = unify_types t1 t2 env in
  output_simplified_types env [t1; t2];
  [@@expect.uncaught_exn {| ("Unification_failure(int, bool)") |}]

