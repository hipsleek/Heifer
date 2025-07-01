open Hipcore
open Hiptypes
open Typedhip
open Types
open Pretty
open Debug

(* TODO Restore all debug output once Pretty_typed has been ported over *)

let fresh_type_var () = TVar (Variables.fresh_variable ())

(* utility functions to help manage the environment via the state monad *)
module State(SType : sig type t end) = struct
  type 'a t = SType.t -> 'a * SType.t
  let return v env = (v, env)
  let bind (op : 'a t) (f : 'a -> 'b t) : 'b t =
    fun env -> 
      let v, env = op env in
      f v env
  let (let*) = bind

  let mutate (f : SType.t -> SType.t) : unit t =
    fun st -> (), f st

  let rec map ~(f:'a -> 'b t) (ls : 'a list) : 'b list t =
    match ls with
    | [] -> return []
    | x::xs -> 
        let* x = f x in
        let* xs = map ~f xs in
        return (x::xs)

  (* monad-aware wrapper around Debug's utilities *)
  module Debug = struct
    let span : (('a * SType.t) presult -> unit) -> (unit -> 'a t) -> 'a t =
      fun show k env ->
        let@ _ = Debug.span show in
        k () env

    let presult_value r = map_presult fst r
    let presult_state r = map_presult snd r

    let (let@) = Debug.(let@)
  end
  
end

module Env_state = State(struct type t = abs_typ_env end)
type 'a using_env = 'a Env_state.t
let span_env = Env_state.Debug.span
let (let@) = Env_state.Debug.(let@)
let return = Env_state.return
let (let*) = Env_state.(let*)

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
    | TVar _ as var, simp | simp, (TVar _ as var) -> 
        TEnv.equate env.equalities var simp;
        (* check for cycles in the equality map *)
        let var_simplified = TEnv.simplify env.equalities var in
        if (compare_typ var var_simplified <> 0) && List.mem var (free_type_vars var_simplified)
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
    (), env
  end


let find_concrete_type = TEnv.concretize

let concrete_type_env abs : typ_env =
  let simpl t = 
    TEnv.simplify abs.equalities t in
  SMap.map simpl abs.vartypes

let get_primitive_type f =
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
      |> Env_state.map ~f:(fun (arg, expected_type) ->
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
  | CIfElse (_, _, _) -> failwith "CIfELse"
  | CWrite (_, _) -> failwith "CWrite"
  | CRef _ -> failwith "CRef"
  | CRead _ -> failwith "CRead"
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
  (* let@ _ = *)
  (*   span_env (fun r -> *)
  (*       debug ~at:5 ~title:"infer_types" "%s : %s -| %s" (string_of_term term) *)
  (*         (string_of_result string_of_term (Env_state.Debug.presult_value r)) *)
  (*         (string_of_result string_of_abs_env (Env_state.Debug.presult_state r))) *)
  (* in *)
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
      |> Env_state.map ~f:(fun (arg, expected_type) ->
          let* arg = infer_types_term arg in
          let* _ = unify_types arg.term_type expected_type in
          return arg)
    in
    return (TApp (f, args), ret_type)
  | Construct (name, args), _ ->
      let type_decl, (constr_params, constr_arg_types) = Globals.type_constructor_decl name in
      let concrete_bindings = List.map (fun param -> (param, fresh_type_var ())) constr_params in
      let concrete_vars = List.map (fun (_, var) -> var) concrete_bindings in
      (* let args, env = List.map2 pair args constr_arg_types *)
      (* |> List.fold_left *)
      (* (fun (typed_args, env) (arg, arg_type) -> *)
      (*   let expected_arg_type = Types.instantiate_type_variables concrete_bindings arg_type in *)
      (*   let typed_arg, env = infer_types_term ~hint:expected_arg_type env arg in *)
      (*   typed_args @ [typed_arg], env) ([], env) in *)
      let* args = List.combine args constr_arg_types
        |> Env_state.map ~f:(fun (arg, arg_type) ->
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
  let* _ = Env_state.mutate simplify_vartypes in
  return {term_desc; term_type}

let rec infer_types_pi pi : pi using_env =
  (* debug ~at:5 ~title:"infer_types_pi" "%s" (string_of_pi pi); *)
  (* let@ _ = *)
  (*      span_env (fun r -> *)
  (*          debug ~at:5 ~title:"infer_types_pi" "%s -| %s" (string_of_pi pi) *)
  (*            (string_of_result string_of_abs_env (Env_state.Debug.presult_state r))) *)
  (*    in *)
  match pi with
  | True | False -> return pi
  | Atomic (op, a, b) -> begin
    let hint = match op with
      | EQ -> None
      | _ -> Some Int
    in
    let* a = infer_types_term a ?hint in
    let* b = infer_types_term b ?hint in
    return (Atomic (op, a, b))
  end
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

