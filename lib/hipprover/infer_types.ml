open Hipcore
open Hiptypes
open Types
open Pretty
open Debug

(* utility functions to help manage the environment via the state monad *)
module State(SType : sig type t end) = struct
  type 'a t = SType.t -> 'a * SType.t
  let return v env = (v, env)
  let bind (op : 'a t) (f : 'a -> 'b t) : 'b t =
    fun env -> 
      let v, env = op env in
      f v env
  let (let*) = bind

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

    let presult_value = map_presult fst
    let presult_state = map_presult snd

    let (let@) = Debug.(let@)
  end
  
end

module Env_state = State(struct type t = abs_typ_env end)
type 'a using_env = 'a Env_state.t
let span_env = Env_state.Debug.span
let (let@) = Env_state.Debug.(let@)
let return = Env_state.return
let (let*) = Env_state.(let*)

(* record the type (or constraints on) of a program variable in the environment *)
let assert_var_has_type v t env =
  match SMap.find_opt v env.vartypes with
  | None -> (), { env with vartypes = SMap.add v t env.vartypes }
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
    (), env

(* record a (nontrivial) equality in the environment *)
let unify_types t1 t2 env =
  debug ~at:5 ~title:"unify" "%s ~ %s" (string_of_type t1) (string_of_type t2);
  if compare_typ t1 t2 = 0 then (), env
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
    (), env)

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

let rec infer_types_core_lang e : typ using_env =
  match e with
  | CValue t -> infer_types_term t
  | CFunCall (f, args) ->
    let arg_types, ret_type = get_primitive_fn_type f in
    (* TODO check for length mismatch? *)
    let* _actual_arg_types =
      List.combine args arg_types
      |> Env_state.map ~f:(fun (arg, expected_type) ->
          let* actual_type = infer_types_term arg in
          let* _ = unify_types actual_type expected_type in
          return actual_type)
    in
    return ret_type
  | CLet (x, e1, e2) ->
    let* t1 = infer_types_core_lang e1 in
    let* _ = assert_var_has_type x t1 in
    infer_types_core_lang e2
  | CSequence (e1, e2) ->
    let* _ = infer_types_core_lang e1 in
    infer_types_core_lang e2
  | CIfELse (_, _, _) -> failwith "CIfELse"
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

and infer_types_term ?(hint : typ option) term : typ using_env =
  let@ _ =
    span_env (fun r ->
        debug ~at:5 ~title:"infer_types" "%s : %s -| %s" (string_of_term term)
          (string_of_result string_of_type (Env_state.Debug.presult_value r))
          (string_of_result string_of_abs_env (Env_state.Debug.presult_state r)))
  in
  match (term, hint) with
  | Const ValUnit, _ -> return Unit
  | Const TTrue, _ | Const TFalse, _ -> return Bool
  | Const (TStr _), _ -> return TyString
  | Const Nil, _ -> return List_int
  | Const (Num _), _ -> return Int
  | TNot a, _ ->
    let* _ = infer_types_term ~hint:Bool a in
    return Bool
  | BinOp (op, a, b), _ ->
      let atype, btype, ret_type = match op with
        | TCons -> Int, List_int, List_int
        | TAnd| TOr -> Bool, Bool, Bool
        | SConcat -> TyString, TyString, TyString
        | Plus | Minus | TTimes | TDiv | TPower -> Int, Int, Int
      in
      let* _ = infer_types_term ~hint:atype a in
      let* _ = infer_types_term ~hint:btype b in
      return ret_type
  (* possibly add syntactic heuristics for types, such as names *)
  | Var v, Some t -> 
      let* _ = assert_var_has_type v t in
      return t
  | Var v, None ->
    let t = (TVar (Variables.fresh_variable v)) in
    let* _ = assert_var_has_type v t in
    return t
  | TLambda (_, _, _, Some _), _
  | TLambda (_, _, _, None), _ -> return Lamb
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
    let* at = infer_types_term ?hint a in
    let* bt = infer_types_term ?hint b in
    let* _ = unify_types at bt in
    return Bool
  end
  | Rel ((GT | LT | GTEQ | LTEQ), a, b), _ ->
    let* _ = infer_types_term ~hint:Int a in
    let* _ = infer_types_term ~hint:Int b in
    return Bool
  | TApp (f, args), _ ->
    let arg_types, ret_type = get_primitive_type f in
    let* _actual_arg_types =
      List.combine args arg_types
      |> Env_state.map ~f:(fun (arg, expected_type) ->
          let* actual_type = infer_types_term arg in
          let* _ = unify_types actual_type expected_type in
          return actual_type)
    in
    return ret_type
  | Construct _, _ -> failwith "constructors unimplemented"
  | TTuple _, _ -> failwith "tuple unimplemented"

let rec infer_types_pi pi : unit using_env =
  (* let@ _ =
       Debug.span (fun r ->
           debug ~at:5 ~title:"infer_types_pi" "%s -| %s" (string_of_pi pi)
             (string_of_result string_of_abs_env r))
     in *)
  match pi with
  | True | False -> return ()
  | Atomic (EQ, a, b) ->
    let* t1 = infer_types_term a in
    let* t2 = infer_types_term b in
    (* Format.printf "EQ %s = %s@." (string_of_term a) (string_of_term b); *)
    unify_types t1 t2
  | Atomic (GT, a, b)
  | Atomic (LT, a, b)
  | Atomic (GTEQ, a, b)
  | Atomic (LTEQ, a, b) -> begin
    let* _ = infer_types_term ~hint:Int a in
    let* _ = infer_types_term ~hint:Int b in
    return ()
  end
  | And (a, b) | Or (a, b) | Imply (a, b) ->
    let* _ = infer_types_pi a in
    infer_types_pi b
  | Not a -> infer_types_pi a
  | Predicate (_, _) -> return ()
  | Subsumption (_, _) -> return ()
