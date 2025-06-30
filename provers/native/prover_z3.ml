open Hipcore
open Debug
open Hiptypes
open Typedhip
open Pretty_typed
open Subst_typed

open Types
open Z3

let list_int_sort ctx =
  let int = Z3.Arithmetic.Integer.mk_sort ctx in
  (* Z3.Z3List.mk_sort ctx (Z3.Symbol.mk_string ctx "List") int *)
  Z3.Z3List.mk_list_s ctx "List" int

let unit_sort ctx =
  let us = Z3.Symbol.mk_string ctx "unit" in
  Z3.Tuple.mk_sort ctx us [] []

type z3_context = {
  ctx: context;
  mutable custom_sorts: Sort.sort TMap.t;
}

let rec z3_sort_of_typ ctx typ =
  let recognizer_name constr_name = 
    let constr_name = match constr_name with
    | "::" -> "cons"
    | "[]" -> "nil"
    | _ -> constr_name in
    "is_" ^ constr_name in
  let constructor_field_names (constr_name, constr_args) = 
    match constr_name with
    | "::" -> ["head"; "tail"] |> List.map (Z3.Symbol.mk_string ctx.ctx)
    | _ -> constr_args 
    |> List.mapi (fun i _arg -> "field_" ^ constr_name ^ "_" ^ (string_of_int i)) 
    |> List.map (Z3.Symbol.mk_string ctx.ctx) in
  let memo f = match TMap.find_opt typ ctx.custom_sorts with
  | Some sort -> sort
  | None -> 
      let result = f ctx typ in
      ctx.custom_sorts <- TMap.add typ result ctx.custom_sorts;
      result
  in
  memo begin fun z3_ctx typ ->
    let {ctx; _} = z3_ctx in
    match typ with
    | Any -> failwith "SMT formulas must be typed"
    | TConstr (type_name, args) ->
        let type_def = try Globals.find_type_decl type_name
          with
            | Not_found -> raise (Invalid_argument (Printf.sprintf "definition for type constructor %s not found" type_name))
        in
        let param_values = List.combine type_def.tdecl_params args in
        begin match type_def.tdecl_kind with
          | Tdecl_record _ -> failwith "Records not supported"
          | Tdecl_inductive constructors ->
            (* NOTE: This cannot handle recursive definitions that recurse on types other
                than themselves (e.g. type ('b, 'a) example = Nil | Other of ('a, 'b) example).
                We'd need to gather all the types that this type relies on, and pass them to mk_constructor_s all at once. *)
            let process_constructor (constr_name, constr_args) = 
              let concrete_constr_args = List.map (instantiate_type_variables param_values) constr_args in
              let field_names = constructor_field_names (constr_name, constr_args) in
              let (arg_sorts, arg_sort_refs) = concrete_constr_args
                |> List.map (fun constr_arg ->
                    if constr_arg = typ
                    then (None, 0)
                    else (Some (z3_sort_of_typ z3_ctx constr_arg), 0)
                  )
                |> List.split 
              in
              Z3.Datatype.mk_constructor_s ctx constr_name (Z3.Symbol.mk_string ctx (recognizer_name constr_name))
                field_names arg_sorts arg_sort_refs in 
            Z3.Datatype.mk_sort_s ctx (string_of_type typ) (List.map process_constructor constructors)
        end
    | Unit -> unit_sort ctx
    | TVar _ (* Any type variables encountered at this point can be instantiated with anything, so just use Int for now. *)
    | Lamb (* case carried over from old term_to_expr *)
    | Int -> Z3.Arithmetic.Integer.mk_sort ctx
    | Bool -> Z3.Boolean.mk_sort ctx
    | TyString -> Z3.Seq.mk_string_sort ctx
    | Arrow _ -> raise (Invalid_argument (Printf.sprintf "z3_sort_of_typ: type %s not supported" (string_of_type typ)))
  end

let get_datatype_func ctx typ s =
  let z3_sort = z3_sort_of_typ ctx typ in
  (* debug ~at:5 ~title:"get_datatype_func" "type %s (sort %s) func %s\n" *)
  (*   (string_of_type typ) (Z3.Sort.to_string z3_sort) s; *)
  let sort_funcs = Z3.Datatype.(get_constructors z3_sort @ get_recognizers z3_sort @ (List.concat (get_accessors z3_sort))) in
  debug ~at:5 ~title:"get_datatype_func functions" "%s"
    (String.concat ", " (List.map Z3.FuncDecl.get_name sort_funcs |> List.map Z3.Symbol.get_string));
  sort_funcs |> List.find_opt (fun func_decl -> (Z3.FuncDecl.get_name func_decl |> Z3.Symbol.get_string) = s)
  
let get_fun_decl ctx s =
  let list_int = list_int_sort ctx in
  match s with
  | "cons" -> (Z3.Z3List.get_cons_decl list_int)
  | "head" -> (Z3.Z3List.get_head_decl list_int)
  | "tail" -> (Z3.Z3List.get_tail_decl list_int)
  | "is_cons" -> (Z3.Z3List.get_is_cons_decl list_int)
  | "is_nil" -> (Z3.Z3List.get_is_nil_decl list_int)
  | _ ->  (* ASK Darius *)
    let intSort = (Z3.Arithmetic.Integer.mk_sort ctx) in 
    if String.compare s "effNo" == 0 then Z3.FuncDecl.mk_func_decl_s ctx "effNo" [intSort] intSort
    else failwith (Format.asprintf "unknown function 1: %s" s)

let rec term_to_expr env z3_ctx t : Z3.Expr.expr =
  (* let@ _ = Debug.span (fun r -> debug ~at:5 ~title:"term_to_expr" "%s : %s ==> %s" (string_of_term t) (string_of_type t.term_type) (string_of_result Expr.to_string r)) in *)
  let {ctx; _} = z3_ctx in
  match t.term_desc with
  | Const (Num n) -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
  | Var v -> Z3.Expr.mk_const_s ctx v (z3_sort_of_typ z3_ctx t.term_type)
  | Const ValUnit ->
    let mk = Z3.Tuple.get_mk_decl (unit_sort ctx) in 
    Z3.Expr.mk_app ctx mk []
  | TLambda _ ->
    (* Format.printf "z3 %s %d@." (string_of_term t) (hash_lambda t); *)
    (* Z3.Arithmetic.Integer.mk_numeral_i ctx (hash_lambda t) *)
    (* FIXME change to use hash lambdas *)
    Z3.Arithmetic.Integer.mk_numeral_i ctx 0
  | Const Nil ->
    Z3.Expr.mk_app ctx (get_datatype_func z3_ctx t.term_type "[]" |> Option.get) []
  (*
  | Gen i          -> Z3.Arithmetic.Real.mk_const_s ctx ("t" ^ string_of_int i ^ "'")
  *)
  | BinOp (SConcat, t1, t2) ->
    let t1' = term_to_expr env z3_ctx t1 in 
    let t2' = term_to_expr env z3_ctx t2 in 
    let res = Z3.Seq.mk_seq_concat ctx [t1'; t2'] in 
    res
  | BinOp (Plus, t1, t2) ->
    (*print_endline ("\n-------\nPlus " ^ string_of_term t);*)
    let t1' = term_to_expr env z3_ctx t1 in 
    let t2' = term_to_expr env z3_ctx t2 in 
    let res = Z3.Arithmetic.mk_add ctx [t1'; t2'] in 


    (*Here!!!! 
    mk_add
    Plus v85, (^ 2 n) ===> Plus (+ (to_real v85) (^ 2 n))
*)

    (*let res = Z3.Arithmetic.Real.mk_real2int ctx res in 
    *)
    
    (*print_endline ("Plus " ^ Expr.to_string t1' ^ ", " ^ Expr.to_string t2');
    print_endline ("Plus " ^ Expr.to_string res );
    *)

    res
  | BinOp (Minus, t1, t2) ->
    Z3.Arithmetic.mk_sub ctx [term_to_expr env z3_ctx t1; term_to_expr env z3_ctx t2]

  | Rel (bop, t1, t2) ->
    (match bop with
    | EQ ->
      Z3.Boolean.mk_eq ctx (term_to_expr env z3_ctx t1) (term_to_expr env z3_ctx t2)
    | GT ->
      Z3.Arithmetic.mk_gt ctx (term_to_expr env z3_ctx t1)
        (term_to_expr env z3_ctx t2)
    | LT ->
      Z3.Arithmetic.mk_lt ctx (term_to_expr env z3_ctx t1)
        (term_to_expr env z3_ctx t2)
    | GTEQ ->
      Z3.Arithmetic.mk_ge ctx (term_to_expr env z3_ctx t1)
        (term_to_expr env z3_ctx t2)
    | LTEQ ->
      Z3.Arithmetic.mk_le ctx (term_to_expr env z3_ctx t1)
        (term_to_expr env z3_ctx t2))
  | Const TTrue -> Z3.Boolean.mk_true ctx
  | Const TFalse -> Z3.Boolean.mk_false ctx
  | Const (TStr s) -> Z3.Seq.mk_string ctx s
  | TNot a -> Z3.Boolean.mk_not ctx (term_to_expr env z3_ctx a)
  | BinOp (TAnd, a, b) ->
    Z3.Boolean.mk_and ctx [term_to_expr env z3_ctx a; term_to_expr env z3_ctx b]
  | BinOp (TOr, a, b) ->
    Z3.Boolean.mk_or ctx [term_to_expr env z3_ctx a; term_to_expr env z3_ctx b]
  | BinOp (TCons, a, b) ->
    (* Z3.Expr.mk_app ctx (get_fun_decl ctx "cons") *)
    (*   (List.map (term_to_expr env z3_ctx) [a; b]) *)
    Z3.Expr.mk_app ctx (get_datatype_func z3_ctx t.term_type "::" |> Option.get)
      (List.map (term_to_expr env z3_ctx) [a; b])
  | TApp ("string_of_int" , [x]) ->
    Z3.Seq.mk_int_to_str ctx (term_to_expr env z3_ctx x)
  | TApp (f, a) ->
    Z3.Expr.mk_app ctx (get_fun_decl ctx f) (List.map (term_to_expr env z3_ctx) a)
  | BinOp (TPower, t1, t2) -> 
    let res = Z3.Arithmetic.mk_power ctx (term_to_expr env z3_ctx t1) (term_to_expr env z3_ctx t2) in 
    (*print_endline ("TPower " ^ Expr.to_string res);*)
    res
  | BinOp (TTimes, t1, t2) -> Z3.Arithmetic.mk_mul ctx [term_to_expr env z3_ctx t1; term_to_expr env z3_ctx t2]
  | BinOp (TDiv, t1, t2) -> Z3.Arithmetic.mk_div ctx (term_to_expr env z3_ctx t1) (term_to_expr env z3_ctx t2)

  | Construct (name, args) -> 
      let type_constructors = Z3.Datatype.get_constructors (z3_sort_of_typ z3_ctx t.term_type) in
      let constr_func = List.find (fun decl -> Z3.Symbol.get_string (Z3.FuncDecl.get_name decl) = name) type_constructors in
      Z3.Expr.mk_app ctx constr_func (List.map (term_to_expr env z3_ctx ) args)
  | TTuple _ -> failwith "term_to_expr"

let rec pi_to_expr env z3_ctx pi: Expr.expr = 
  (* let@ _ = Debug.span (fun r -> debug ~at:5 ~title:"pi_to_expr" "%s ==> %s" (string_of_pi pi) (string_of_result Expr.to_string r)) in *)
  let {ctx; _} = z3_ctx in
  match pi with 
  | True -> Z3.Boolean.mk_true ctx
  | False -> Z3.Boolean.mk_false ctx
  | Atomic (GT, t1, t2) ->
    let t1 = term_to_expr env z3_ctx t1 in
    let t2 = term_to_expr env z3_ctx t2 in
    Z3.Arithmetic.mk_gt ctx t1 t2
  | Atomic (GTEQ, t1, t2) ->
    let t1 = term_to_expr env z3_ctx t1 in
    let t2 = term_to_expr env z3_ctx t2 in
    Z3.Arithmetic.mk_ge ctx t1 t2
  | Atomic (LT, t1, t2) ->
    let t1 = term_to_expr env z3_ctx t1 in
    let t2 = term_to_expr env z3_ctx t2 in
    Z3.Arithmetic.mk_lt ctx t1 t2
  | Atomic (LTEQ, t1, t2) ->
    let t1 = term_to_expr env z3_ctx t1 in
    let t2 = term_to_expr env z3_ctx t2 in
    Z3.Arithmetic.mk_le ctx t1 t2
  (* | IsCons (v, t1, t2) -> *)
    (* failwith "" *)
  | Atomic (EQ, t1, t2) ->
    let t1 = term_to_expr env z3_ctx t1 in
    let t2 = term_to_expr env z3_ctx t2 in
    (*print_endline ("\n======\nAtomic EQ " ^ Expr.to_string t1);
    print_endline ("Atomic EQ " ^ Expr.to_string t2);
    *)
    let res = Z3.Boolean.mk_eq ctx t1 t2 in 
    res

  | Imply (p1, p2) ->
    Z3.Boolean.mk_implies ctx (pi_to_expr env z3_ctx p1) (pi_to_expr env z3_ctx p2)
  | Predicate (_, _) -> failwith "pi_to_expr"
  | Subsumption (_, _) -> pi_to_expr env z3_ctx True
  (*
  | Atomic (op, t1, t2) -> (
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      match op with
      | Eq -> Z3.Boolean.mk_eq ctx t1 t2
      | LT -> Z3.Arithmetic.mk_lt ctx t1 t2
      | Le -> Z3.Arithmetic.mk_le ctx t1 t2
      | GT -> Z3.Arithmetic.mk_gt ctx t1 t2
      | Ge -> Z3.Arithmetic.mk_ge ctx t1 t2)
      *)
  | And (pi1, pi2) ->
    Z3.Boolean.mk_and ctx [pi_to_expr env z3_ctx pi1; pi_to_expr env z3_ctx pi2]
  | Or (pi1, pi2) ->
    Z3.Boolean.mk_or ctx [pi_to_expr env z3_ctx pi1; pi_to_expr env z3_ctx pi2]
  (*| Imply (pi1, pi2)    -> Z3.Boolean.mk_implies ctx (pi_to_expr env ctx pi1) (pi_to_expr env ctx pi2)
  *)
  | Not pi -> Z3.Boolean.mk_not ctx (pi_to_expr env z3_ctx pi)

(* let z3_query (_s : string) =
   (* Format.printf "z3: %s@." _s; *)
   () *)

(* let _test () =
  let ctx = Z3.mk_context [] in
  (* let int = Z3.Arithmetic.Integer.mk_sort ctx in *)
  let list_int = list_int_sort ctx in
  let left =
    (* Z3.Boolean.mk_eq ctx
       (Z3.Arithmetic.Integer.mk_const_s ctx "a")
       (Z3.Arithmetic.Integer.mk_numeral_i ctx 1) *)
    Z3.Boolean.mk_and ctx
      [
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "a" list_int)
          (Z3.Z3List.nil list_int);
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "c" list_int)
          (Z3.Z3List.nil list_int);
      ]
  in
  let right =
    (* Z3.Boolean.mk_eq ctx
       (Z3.Arithmetic.Integer.mk_const_s ctx "b")
       (Z3.Arithmetic.Integer.mk_numeral_i ctx 1) *)
    Z3.Boolean.mk_and ctx
      [
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "b" list_int)
          (Z3.Z3List.nil list_int);
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "d" list_int)
          (Z3.Z3List.nil list_int);
      ]
  in
  let expr =
    Z3.Boolean.mk_not ctx
      (Z3.Boolean.mk_implies ctx left
         Z3.Quantifier.(
           expr_of_quantifier
             (mk_exists_const ctx
                [
                  Z3.Expr.mk_const_s ctx "b" list_int;
                  Z3.Expr.mk_const_s ctx "d" list_int
                  (* Z3.Expr.mk_const_s ctx "b" int *)
                  (* Z3.Arithmetic.Integer.mk_const_s ctx "b"; *);
                ]
                right None [] [] None None)))
  in
  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [expr];
  debug ~at:4 ~title:"z3 expr" "%s" (Expr.to_string expr);
  debug ~at:4 ~title:"z3 solver" "%s" (Solver.to_string solver);
  let sat = Solver.check solver [] == Solver.SATISFIABLE in
  debug ~at:4 ~title:"sat?" "%b" sat;
  match Solver.get_model solver with
  | None -> debug ~at:4 ~title:"no model" ""
  | Some m -> debug ~at:4 ~title:"model" "%s" (Model.to_string m) *)

let new_context z3_config = {
  ctx = mk_context z3_config;
  custom_sorts = TMap.empty;
}

let check_sat f =
  let@ _ = Globals.Timing.(time z3) in 
  let cfg =
    let debug = false in
    (if debug then [("model", "false")] else []) @ [("proof", "false")]
  in
  let ctx = new_context cfg in
  Z3.Params.update_param_value ctx.ctx "timeout" "5000";
  let expr =
    let@ _ = Debug.span (fun _ -> debug ~at:4 ~title:"build formula" "") in
    f ctx
  in
  (* let goal = Goal.mk_goal ctx true true false in *)
  (* Goal.add goal [ expr ]; *)
  (* let goal = Goal.simplify goal None in *)
  (* if debug then Format.printf "goal: %s@." (Goal.to_string goal); *)
  let solver = Solver.mk_simple_solver ctx.ctx in
  Solver.add solver [expr];
  (* print both because the solver does some simplification *)
  debug ~at:4 ~title:"z3 expr" "%s\n(check-sat)" (Expr.to_string expr);
  let@ _ =
    Debug.span (fun _ -> debug ~at:5 ~title:"z3 solver" "%s\n(check-sat)" (Solver.to_string solver))
  in
  (* Format.printf "%s@." (Solver.to_string solver); *)
  (* Format.printf "%s@." (Expr.to_string expr); *)
  let status =
    let@ _ =
      Debug.span (fun r ->
          debug ~at:4
            ~title:"z3 sat check"
            "%s" (string_of_result Solver.string_of_status r))
    in
    Solver.check solver []
  in 
  (* (match Solver.get_model solver with
  | None -> debug ~at:4 ~title:"no model" ""
  | Some m -> debug ~at:4 ~title:"model" "%s" (Model.to_string m)); *)
  status

(* let check env pi =
  debug ~at:4 ~title:"z3 sat, pi" "%s" (string_of_pi pi);
  check_sat (fun ctx -> pi_to_expr env ctx pi) *)

(* see https://discuss.ocaml.org/t/different-z3-outputs-when-using-the-api-vs-cli/9348/3 and https://github.com/Z3Prover/z3/issues/5841 *)
let ex_quantify_expr env vars ctx e =
  let binders = vars
    |> List.map (fun var ->
        let t = SMap.find_opt var env
        |> Option.value ~default:Unit
        in (var, t))
  in
  match vars with
  | [] -> e
  | _ :: _ ->
    Z3.Quantifier.(
      expr_of_quantifier
        (mk_exists_const ctx.ctx
           (List.map (fun v -> term_to_expr env ctx (var_of_binder v)) binders)
           e None [] [] None None))

  let type_to_sort ctx (t:typ) : Sort.sort =
    match t with
    | Any -> failwith "Formulas at the SMT level must be typed"
    | Unit -> unit_sort ctx
    (* | TConstr of string * typ list *)
    | Int -> Z3.Arithmetic.Integer.mk_sort ctx
    | TConstr (_, _) -> failwith "TConstr"
    | Bool -> failwith "Bool"
    | TyString -> failwith "TyString"
    | Lamb -> failwith "Lamb"
    | Arrow (_, _) -> failwith "Arrow"
    | TVar _ -> failwith "TVar"

  let core_lang_to_expr : core_lang -> Expr.expr = fun e ->
    (* Format.printf "expr %s@." (Pretty.string_of_core_lang e); *)
    match e.core_desc with
    | CLet _ ->
      failwith "let"
    | CSequence _ ->
      failwith "sequence"
    | CValue _ ->
      failwith "value"
    | CIfElse (_, _, _) -> failwith "unimplemented CIfELse"
    | CMatch (_, _, _scr, [], _cases) ->
      (* x :: xs -> e is represented as ("::", [x, xs], e) *)
      (* and constr_cases = (string * string list * core_lang) list *)
      failwith "match"
    | CFunCall (s, _args) when Globals.is_pure_fn_defined s ->
      failwith "unimplemented CFunCall"
    | CFunCall (s, _) -> failwith (Format.asprintf "unknown function %s" s)
    | CWrite (_, _) -> failwith "unimplemented CWrite"
    | CRef _ -> failwith "unimplemented CRef"
    | CRead _ -> failwith "unimplemented CRead"
    | CAssert (_, _) -> failwith "unimplemented CAssert"
    | CPerform (_, _) -> failwith "unimplemented CPerform"
    | CMatch (_, _, _, _, _) -> failwith "unimplemented effect CMatch"
    | CResume _ -> failwith "unimplemented CResume"
    | CLambda (_, _, _) -> failwith "unimplemented CLambda"
    | CShift _ | CReset _ -> failwith "TODO shift and reset expr_to_why3 "

  let pure_fn_to_logic_fn ctx (pure_fn: pure_fn_def) =
    let decl =
      let param_types =
        pure_fn.pf_params
          |> List.map snd
          |> List.map (type_to_sort ctx)
      in
      let ret_type = pure_fn.pf_ret_type |> type_to_sort ctx in
      FuncDecl.mk_rec_func_decl_s ctx
        pure_fn.pf_name param_types ret_type
    in
    let params =
      pure_fn.pf_params
      (* TODO handle other types *)
      |> List.map (fun (n, _ty) -> Z3.Arithmetic.Integer.mk_const_s ctx n)
    in
    let body = core_lang_to_expr pure_fn.pf_body in
    FuncDecl.add_rec_def ctx decl params body

(* this is a separate function which doesn't cache results because exists isn't in pi *)
let entails_exists env p1 vs p2 =
  (* debug ~at:4 ~title:"z3 valid" "%s => ex %s. %s\n%s" (string_of_pi p1) *)
  (*   (String.concat " " vs) (string_of_pi p2) (string_of_typ_env env); *)
  let f ctx =
    let r =
      Z3.Boolean.mk_not ctx.ctx
        (Z3.Boolean.mk_implies ctx.ctx (pi_to_expr env ctx p1)
           (ex_quantify_expr env vs ctx (pi_to_expr env ctx p2)))
    in
    (* Format.printf "oblig: %s@." (Expr.to_string r); *)
    r
  in
  match check_sat f with
  | UNSATISFIABLE -> Provers_common.Valid
  |	UNKNOWN -> Provers_common.Unknown "Z3 returned UNKNOWN"
  |	SATISFIABLE -> Provers_common.Invalid
