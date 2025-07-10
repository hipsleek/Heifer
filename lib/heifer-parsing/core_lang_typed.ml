(**
  This version of Core_lang uses Compiler-libs's built in Typedtree instead
  as a basis for transformation.
   *)

open Ocaml_compiler.Ocaml_common

module Compiler_types = Types

open Typedtree
open Asttypes
(* get rid of the alias *)
type string = label
open Hipcore
open Hiptypes
open Typedhip

exception Foo of string

let rec get_tactic e =
  let open Parsetree in
  match e with
  | { pexp_desc = Pexp_ident { txt = Lident "unfold_right"; _ }; _ } ->
    [Unfold_right]
  | { pexp_desc = Pexp_ident { txt = Lident "unfold_left"; _ }; _ } ->
    [Unfold_left]
  | { pexp_desc = Pexp_apply ({pexp_desc = Pexp_ident { txt = Lident "apply"; _ }; _}, [(_, {pexp_desc = Pexp_ident { txt = Lident lem; _ }; _})]); _ } ->
    [Apply lem]
  | { pexp_desc = Pexp_apply ({pexp_desc = Pexp_ident { txt = Lident "case"; _ }; _}, [(_, {pexp_desc = Pexp_constant {pconst_desc = Pconst_integer (i, _); _}; _}); (_, sub)]); _ } ->
    let t = List.hd (get_tactic sub) in
    [Case (int_of_string i, t)]
  | { pexp_desc = Pexp_sequence (e1, e2); _ } ->
    let a = get_tactic e1 in
    let b = get_tactic e2 in
    a @ b
  | _ -> []

let collect_annotations attrs =
  let open Parsetree in
  List.fold_right
    (fun c t ->
      match c.attr_payload with
      | PStr [{ pstr_desc = Pstr_eval (e, _); _ }] when String.equal "proof" c.attr_name.txt -> get_tactic e
      | _ -> t)
    attrs []

let string_of_p_constant con : string =
  match con with 
  | Const_char i -> String.make 1 i
  | Const_string (i, _, None) -> i
  | Const_string (i, _, Some delim) -> i ^ delim
  | Const_int i -> (string_of_int i)
  | _ -> "string_of_p_constant"

let string_of_arg_label a = 
  match a with 
  | Nolabel -> ""
  | Labelled str -> str (*  label:T -> ... *)
  | Optional str -> "?" ^ str (* ?label:T -> ... *)

let rec string_of_core_type (p:core_type) :string =
  match p.ctyp_desc with 
  | Ttyp_any -> "_"
  | Ttyp_var str -> str
  | Ttyp_arrow (a, c1, c2) -> string_of_arg_label a ^  string_of_core_type c1 ^ " -> " ^ string_of_core_type c2 ^"\n"
  | Ttyp_constr (_, l, c_li) -> 
    List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)^
    List.fold_left (fun acc a -> acc ^ string_of_core_type a) "" c_li
  | Ttyp_tuple (ctLi) -> "(" ^
    (List.fold_left (fun acc a -> acc ^ "," ^ string_of_core_type a ) "" ctLi) ^ ")"

  | Ttyp_poly (str_li, c) -> 
    "type " ^ List.fold_left (fun acc a -> acc ^ a) "" str_li ^ ". " ^
    string_of_core_type c 


  | _ -> "\nlsllsls\n"
let rec string_of_pattern (p) : string = 
  match p.pat_desc with 
  | Tpat_any -> "_"
  (* _ *)
  | Tpat_var (_, str, _) -> str.txt
  (* x *)
  | Tpat_constant con -> string_of_p_constant con
  (* (P : T) *)
  | Tpat_construct (l, _, params, _) ->  
    List.fold_left (fun acc a -> acc ^ " " ^ (string_of_pattern a)) (String.concat " " (Longident.flatten l.txt)) params
    (* ^ string_of_pattern p1 *)
  | _ -> Format.asprintf "string_of_pattern: %a\n" Pprintast.pattern (Untypeast.untype_pattern p)

let rec hip_type_of_type_expr (texpr: Compiler_types.type_expr) =
  match (Compiler_types.get_desc texpr) with
  | Tvar (Some var) -> TVar var
  | Tvar (None) -> Types.new_type_var ()
  (* TODO: This does not preserve argument labels, because Heifer's type system does not model them. *)
  | Tarrow (_, t1, t2, _) -> Arrow (hip_type_of_type_expr t1, hip_type_of_type_expr t2)
  (* TODO implement ref types *)
  | Tconstr (path, [], _) -> begin
      match (Path.name path) with
      | "int" -> Int
      | "bool" -> Bool
      | "string" -> TyString
      | "unit" -> Unit
      | other -> TConstr (other, [])
    end
  | Tconstr (path, args, _) -> begin
    TConstr (Path.name path, List.map hip_type_of_type_expr args)
    end
  | _ -> failwith "Unknown type expression"
  

let rec expr_to_term (expr:expression) : term =
  let term_desc = 
    match expr.exp_desc with
    | Texp_constant (Const_int num) -> Const (Num num )
    | Texp_ident (_, ident, _) -> Var (String.concat "." (Longident.flatten ident.txt))
    | Texp_apply ({exp_desc = Texp_ident (_, {txt=Lident i; _}, _); _}, [(_, Some a); (_, Some b)]) ->
        let op = begin match i with
        | "^" -> fun lhs rhs -> BinOp (SConcat, lhs, rhs)
        | "+" -> fun lhs rhs -> BinOp (Plus, lhs, rhs)
        | "-" -> fun lhs rhs -> BinOp (Minus, lhs, rhs)
        | "&&" -> fun lhs rhs -> BinOp (TAnd, lhs, rhs)
        | "<=" -> fun lhs rhs -> Rel (LTEQ, lhs, rhs)
        | ">=" -> fun lhs rhs -> Rel (GTEQ, lhs, rhs)
        | ">" -> fun lhs rhs -> Rel (GT, lhs, rhs)
        | "<" -> fun lhs rhs -> Rel (LT, lhs, rhs)
        | "=" -> fun lhs rhs -> Rel (EQ, lhs, rhs)
        | _ -> failwith (Format.asprintf "unknown op %s" i)
        end
        in
        op (expr_to_term a) (expr_to_term b)
    | _ -> failwith (Format.asprintf "unknown term %a" Pprintast.expression (Untypeast.untype_expression expr))
  in
  let term_type = hip_type_of_type_expr expr.exp_type in
  {term_desc; term_type}

(* TODO: expr_to_formula *)
let rec expr_to_formula (expr : expression) : pi * kappa =
  match expr.exp_desc with
  | Texp_apply ({exp_desc = Texp_ident (_, {txt=Lident i; _}, _); _}, [(_, Some a); (_, Some b)]) ->
    begin match i with
    | "=" ->
      begin match a.exp_desc with
      | Texp_apply({exp_desc = Texp_ident(_, {txt=Lident "!"; _}, _); _}, [_, Some {exp_desc = Texp_ident(_, {txt=Lident p; _}, _); _}]) -> 
          True, PointsTo (p, expr_to_term b)
      | _ -> Atomic (EQ, expr_to_term a, expr_to_term b), EmptyHeap
      end
    | "<" -> Atomic (LT, expr_to_term a, expr_to_term b), EmptyHeap
    | "<=" -> Atomic (LTEQ, expr_to_term a, expr_to_term b), EmptyHeap
    | ">" -> Atomic (GT, expr_to_term a, expr_to_term b), EmptyHeap
    | ">=" -> Atomic (GTEQ, expr_to_term a, expr_to_term b), EmptyHeap
    | "&&" ->
      let p1, h1 = expr_to_formula a in
      let p2, h2 = expr_to_formula b in
      And (p1, p2), SepConj (h1, h2)
    | "||" -> 
      let p1, h1 = expr_to_formula a in
      let p2, h2 = expr_to_formula b in
      Or (p1, p2), SepConj (h1, h2)
    | "-->" ->
      let v =
        match (expr_to_term a).term_desc with
        | Var s -> s
        | _ -> failwith (Format.asprintf "invalid lhs of points to: %a" Pprintast.expression (Untypeast.untype_expression a))
      in
      True, PointsTo (v, expr_to_term b)
    | _ ->
      failwith (Format.asprintf "unknown binary op: %s" i)
    end
  | Texp_apply ({exp_desc = Texp_ident (_, {txt=Lident i; _}, _); _}, [(_, _a)]) ->
      begin match i with
      (* | "not" -> Not (expr_to_formula a) *)
      | _ -> failwith (Format.asprintf "unknown unary op: %s" i)
      end
  | Texp_construct ({txt=Lident "true"; _}, _, []) -> True, EmptyHeap
  | Texp_construct ({txt=Lident "false"; _}, _, []) -> False, EmptyHeap
  | _ ->
    failwith (Format.asprintf "unknown kind of formula: %a" Pprintast.expression (Untypeast.untype_expression expr))



(*
   let f (a:int) (b:string) : bool = c

   is actually

   let f = fun (a:int) -> fun (b:string) -> (c:bool)

   This recurses down the funs non-tail-recursively to collect all variable names, their types, the return type, and the body.
*)
let collect_param_info rhs =
    let rec return_of_arrow_type typ =
      match (Compiler_types.get_desc typ) with
      | Tarrow (_, _, ret, _) -> return_of_arrow_type ret
      | _ -> typ
    in
    (* TODO allow let f : int -> string -> bool = fun a b -> c *)
    let traverse_to_body e =
      match e.exp_desc with
      | Texp_function (params, Tfunction_body body) ->
        let extract_typedtree_param fp = 
          let pat = match fp.fp_kind with
          | Tparam_pat pat | Tparam_optional_default (pat, _) -> pat
          in
          match pat.pat_desc with
          | Tpat_var (_, {txt = name; _}, _) -> Some (name, pat.pat_type)
          | Tpat_alias (_, _, {txt = name; _}, _) -> Some (name, pat.pat_type)
          (* unknown; getnerate a placeholder for this argument *)
          | _ -> Some ("_" ^ Variables.fresh_variable (), pat.pat_type)
        in
        let params, param_types = params |> List.filter_map extract_typedtree_param |> List.split
        in
        let ret_type = return_of_arrow_type e.exp_type in
        (params, body, (List.map hip_type_of_type_expr param_types, hip_type_of_type_expr ret_type))
      | _ ->
        (* we have reached the end *)
        ([], e, ([], hip_type_of_type_expr e.exp_type))
    in
    let names, body, types = traverse_to_body rhs in
    names, body, types

(* Given a list of currently bound names, and a Typedtree expression, convert it to a
   core language statement. *)
(* TODO handle missing cases *)
let rec transformation (bound_names:string list) (expr:expression) : core_lang =
  let exp_hip_type = hip_type_of_type_expr expr.exp_type in
  let clang_with_expr_type core_desc = {core_desc; core_type = exp_hip_type} in
  let term_with_expr_type term_desc = {term_desc; term_type = exp_hip_type} in
  let true_term = {term_desc = Const TTrue; term_type = Bool} in
  let false_term = {term_desc = Const TFalse; term_type = Bool} in
  match expr.exp_desc with 
  | Texp_ident (_, {txt=Lident i; _}, _) ->
      CValue (Var i |> term_with_expr_type) |> clang_with_expr_type
  | Texp_construct ({txt=Lident "true"; _}, _, []) ->
      CValue true_term |> clang_with_expr_type
  | Texp_construct ({txt=Lident "false"; _}, _, []) ->
      CValue false_term |> clang_with_expr_type
  | Texp_constant c ->
    begin match c with
    | Const_int i -> CValue (Const (Num i) |> term_with_expr_type) |> clang_with_expr_type
    | Const_string (s, _, _) -> CValue (Const (TStr s) |> term_with_expr_type) |> clang_with_expr_type
    | _ -> failwith (Format.asprintf "unknown kind of constant: %a" Pprintast.expression (Untypeast.untype_expression expr))
    end
  (* lambda *)
  | Texp_function (_params, _) ->
    (* see also: Pexp_fun case below in transform_str *)
    let spec = Annotation.extract_spec_attribute expr.exp_attributes in
    (* types aren't used because lambdas cannot be translated to pure functions *)
    let formals, body, (param_types, return_type) = collect_param_info expr in
    let e = transformation (formals @ bound_names) body in
    let bound_vars = List.combine formals param_types
      |> List.map (fun (name, typ) -> Retypehip.binder_of_ident ~typ name) in

    (* typecheck the specifications *)
    let spec = spec |> Option.map (fun spec ->
      let spec, _ = Hipprover.Infer_types.(
        with_empty_env begin
          with_vartypes (List.to_seq ["res", return_type]) begin
            infer_types_staged_spec (Hipcore.Retypehip.retype_staged_spec spec)
          end
        end
      ) 
      in spec)
    in
    CLambda (bound_vars, spec, e) |> clang_with_expr_type

  (* shift and shift0 *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, args) when List.mem name ["shift"; "shift0"] ->
    begin match List.map snd args with
    | [Some {exp_desc = Texp_function ([{ fp_param = k; fp_kind = Tparam_pat {pat_type; _}; _}], Tfunction_body body); _}] ->
      CShift (name = "shift", (Ident.name k, hip_type_of_type_expr pat_type), transformation bound_names body) |> clang_with_expr_type
    | _ ->  failwith "invalid shift args"
    end
  (* reset *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident "reset"; _}, _); _}, args) ->
    begin match args with
    | [_, Some body] ->
      CReset (transformation bound_names body) |> clang_with_expr_type
    | _ ->  failwith "invalid reset args"
    end
  (* perform *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, [_, Some {exp_desc=Texp_construct ({txt=Lident eff; _}, _, args); _}]) when name = "!" ->
      begin match args with
      | a::_ -> transformation bound_names a |> maybe_var (fun v -> CPerform (eff, Some v) |> clang_with_expr_type)
      | [] -> CPerform (eff, None) |> clang_with_expr_type
    end
  (* continue *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, [_, Some _k; _, Some e]) when name = "continue" ->
      transformation bound_names e |> maybe_var (fun v -> CResume [v] |> clang_with_expr_type)

  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, args) when name = "continue" || name = "resume" ->
    (*print_endline (List.fold_left  (fun acc a -> acc ^ ", " ^ a) "" bound_names); *)
    let args = List.filter_map (fun (label, arg) -> Option.map (fun arg -> (label, arg)) arg) args in
    let rec loop vars args =
      match args with
      | [] -> CResume (List.rev vars) |> clang_with_expr_type
      | (_, a) :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  
  (* dereference *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, [_, Some {exp_desc=Texp_ident (_, {txt=Lident v;_}, _); _}]) when name = "!" ->
      CRead v |> clang_with_expr_type
  (* ref *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, [_, Some addr]) when name = "ref" ->
      transformation bound_names addr |> maybe_var (fun v -> CRef v |> clang_with_expr_type)
  (* assign *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, [_, Some {exp_desc=Texp_ident (_, {txt=Lident addr;_}, _); _}; _, Some value]) when name = ":=" ->
      transformation bound_names value |> maybe_var (fun v -> {core_desc = CWrite (addr, v); core_type = Unit})
  (* transparent *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Ldot (Lident "Sys", "opaque_identity"); _}, _); _}, [_, Some a]) ->
    (* ignore this *)
    transformation bound_names a
  (* nil *)
  | Texp_construct ({txt=Lident "[]"; _}, _, []) ->
      {core_desc = CValue {term_desc = Construct ("[]", []); term_type = exp_hip_type}; core_type = exp_hip_type}
  (* unit *)
  | Texp_construct ({txt=Lident "()"; _}, _, []) ->
      {core_desc = CValue ({term_desc = Const ValUnit; term_type = Unit}); core_type = exp_hip_type}
  (* arbitrary constructors *)
  | Texp_construct ({txt = Lident name; _}, _, args) ->
    (* this is almost the same as the next case. can't be unified because the pattern has a different type *)
    let rec loop vars args =
      match args with
      | [] -> CValue (Construct (name, List.rev vars) |> term_with_expr_type) |> clang_with_expr_type
      |  a :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  (* primitive or invocation of higher-order function passed as argument *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, args) when List.mem name bound_names || List.mem name primitive_functions ->
    (* TODO this doesn't model ocaml's right-to-left evaluation order *)
    let rec loop vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars) |> clang_with_expr_type
      | (_, Some a) :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop (v :: vars) args1)
      (* skip over omitted arguments for now *)
      | _ :: args1 -> loop vars args1
    in
    loop [] args
  | Texp_apply (f, args) ->
    let args = args |> List.filter_map (fun (label, expr) -> match expr with 
      | Some value -> Some (label, value) 
      | _ -> None) in
    (* handles both named/unknown function calls, e.g. printf, and applications of compound expressions, which get named *)
    let rec loop name vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars) |> clang_with_expr_type 
      | (_, a) :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop name (v :: vars) args1)
    in
    transformation bound_names f |> maybe_var (fun f1 ->
      match f1.term_desc with
      | Var f2 -> loop f2 [] args
      | _ -> failwith "attempt to apply non-function?")
  | Texp_sequence (a, b) ->
      let a = transformation bound_names a in
      let b = transformation bound_names b in
      CSequence (a, b) |> clang_with_expr_type
  | Texp_assert (e, _) ->
    let p, k = expr_to_formula e in
    {core_desc = CAssert (p, k); core_type = Unit}
  | Texp_let (_rec, vb::_vbs, e) ->
    let var_name = string_of_pattern (vb.vb_pat) in 
    let exprIn = vb.vb_expr in 
    let exprIn = transformation bound_names exprIn in
    if String.equal var_name "res" then
      failwith (Format.asprintf "cannot name variable res");
    CLet ((var_name, exprIn.core_type), exprIn, transformation bound_names e) |> clang_with_expr_type 
  | Texp_ifthenelse (if_, then_, Some else_) ->
    let expr = transformation bound_names if_ in 
    (match expr.core_desc with 
    | CValue v -> (CIfElse ((Atomic (EQ, v, true_term)), transformation bound_names then_, transformation bound_names else_)) |> clang_with_expr_type
    | CFunCall (name, [a;b]) -> 
      if String.compare name "==" ==0 then 
        CIfElse ((Atomic (EQ, a, b)), transformation bound_names then_, transformation bound_names else_) |> clang_with_expr_type
      else 
        let v = Variables.fresh_variable "let" in
        let rest_Expr =  CIfElse ((Atomic (EQ, {term_desc = Var v; term_type = expr.core_type}, true_term)), transformation bound_names then_, transformation bound_names else_) |> clang_with_expr_type in 
        CLet ((v, expr.core_type), expr, rest_Expr) |> clang_with_expr_type
    | _ -> 
      let v = Variables.fresh_variable "let" in
      let rest_Expr =  CIfElse ((Atomic (EQ,{term_desc = Var v; term_type = expr.core_type}, true_term)), transformation bound_names then_, transformation bound_names else_) |> clang_with_expr_type in 
      CLet ((v, expr.core_type), expr, rest_Expr) |> clang_with_expr_type
    )
  | Texp_match (e, computation_cases, value_cases, _) ->
    let effs =
      value_cases |> List.filter_map (fun c ->
        begin match c.c_lhs.pat_desc with
        | Tpat_construct ({txt=Lident eff_name; _}, _, eff_args, _) ->
          let label, arg_binder =
            let arg =
              match eff_args with
              | a::_ -> Some (string_of_pattern a, hip_type_of_type_expr a.pat_type)
              | _ -> None
            in
         eff_name, arg
          in
          let spec = Annotation.extract_spec_attribute c.c_lhs.pat_attributes
              |> Option.map Retypehip.retype_staged_spec
              |> Option.map (fun spec ->
                  let open Hipprover.Infer_types in
                  let new_types = match arg_binder with
                  | Some (arg, arg_type) -> [arg, arg_type]
                  | None -> []
                  in
                  let spec, _ =
                    with_empty_env begin
                      with_vartypes (List.to_seq new_types) begin
                        infer_types_staged_spec spec
                      end
                    end
                  in
                  spec
              )
         in
          Some (label, Option.map Untypehip.ident_of_binder arg_binder, spec, transformation bound_names c.c_rhs)
        | _ -> failwith (Format.asprintf "unknown kind of effect constructor pattern: %a" Pprintast.pattern (Untypeast.untype_pattern c.c_lhs))
        end
      )
    in
    let pattern_cases = 
      computation_cases |> List.map (fun c ->
        match c.c_lhs.pat_desc with
        | Tpat_value value_arg ->
            let pat = (value_arg :> value general_pattern) in 
            let rec transform_pattern pat : Typedhip.pattern = 
              let pattern_desc = match pat.pat_desc with
              | Tpat_construct ({txt=constr; _}, _, args, _) ->
                  let subpatterns = List.map transform_pattern args in
                  PConstr (String.concat "." (Longident.flatten constr), subpatterns)
              | Tpat_var (ident, _, _) -> (PVar (Ident.name ident, hip_type_of_type_expr pat.pat_type))
              | Tpat_alias (pat, _, {txt = name; _}, _) -> PAlias (transform_pattern pat, name)
              | Tpat_any -> PAny
              | _ -> failwith (Format.asprintf "Unsupported pattern %a" Pprintast.pattern (Untypeast.untype_pattern pat))
              in
              let pat = {pattern_desc; pattern_type = hip_type_of_type_expr pat.pat_type} in
              pat
            in
            { ccase_pat = transform_pattern pat;
              ccase_guard = Option.map expr_to_term c.c_guard;
              ccase_expr = transformation bound_names c.c_rhs }
        | _ -> failwith "Unknown pattern" )
    in
    {core_desc = CMatch (Deep, None, transformation bound_names e, effs, pattern_cases); core_type = exp_hip_type}
  | _ -> 
    (*if String.compare (Pprintast.string_of_expression (Untypeast.untype_expression expr)) "Obj.clone_continuation k" == 0 then (* ASK Darius*)*)
    (*CValue (Var "k")*)
    (*else *)
      {core_desc = CValue {term_desc = Const ValUnit; term_type = Unit}; core_type = Unit}
    (* failwith (Format.asprintf "expression not in core language: %a" Pprintast.expression expr)  *)
    (* (Format.printf "expression not in core language: %a@." ({pat_desc = Tpat_construct ({txt = Lident eff_name}, _, _, _); _}Printast.expression 0) expr; failwith "failed") *)

(** If e is not a [CValue], converts the core language expression returned by [f e] into
    [let v = e in expr], where [expr] is the expression returned by [f (Var v)]. Useful
    for creating intermediate variables when generating core language expressions. *)
and maybe_var (f : Typedhip.term -> Typedhip.core_lang) e =
  (* generate fewer unnecessary variables *)
  match e.core_desc with
  | CValue v -> f v
  | _ ->
    let v = Variables.fresh_variable "let" in
    let let_body = f {term_desc = Var v; term_type = e.core_type} in
    {core_desc = CLet ((v, e.core_type), e, let_body); core_type = let_body.core_type}


let string_of_expression_kind (expr:Parsetree.expression_desc) : string = 
  match expr with 
  | Pexp_ident _ -> "Pexp_ident"
  | Pexp_constant _ -> "Pexp_constant"
  | Pexp_let _ -> "Pexp_let"
  | Pexp_function _ -> "Pexp_function"
  | Pexp_apply _ -> "Pexp_apply"
  | Pexp_match _ -> "Pexp_match"
  | Pexp_try _ -> "Pexp_try"
  | Pexp_tuple _ -> "Pexp_tuple"
  | Pexp_construct _ -> "Pexp_construct"
  | Pexp_variant _ -> "Pexp_variant"
  | Pexp_record _ -> "Pexp_record"
  | Pexp_field _ -> "Pexp_field"
  | Pexp_setfield _ -> "Pexp_setfield"
  | Pexp_array _ -> "Pexp_array"
  | Pexp_ifthenelse _ -> "Pexp_ifthenelse"
  | Pexp_sequence _ -> "Pexp_sequence"
  | Pexp_while _ -> "Pexp_while"
  | Pexp_for _ -> "Pexp_for"
  | Pexp_constraint _ -> "Pexp_constraint"
  | Pexp_coerce _ -> "Pexp_coerce"
  | Pexp_send _ -> "Pexp_send"
  | Pexp_new _ -> "Pexp_new"
  | Pexp_setinstvar _ -> "Pexp_setinstvar"
  | Pexp_override _ -> "Pexp_override"
  | Pexp_letmodule _ -> "Pexp_letmodule"
  | Pexp_letexception _ -> "Pexp_letexception"
  | Pexp_assert _ -> "Pexp_assert"
  | Pexp_lazy _ -> "Pexp_lazy"
  | Pexp_poly _ -> "Pexp_poly"
  | Pexp_object _ -> "Pexp_object"
  | Pexp_newtype _ -> "Pexp_newtype"
  | Pexp_pack _ -> "Pexp_pack"
  | Pexp_open _ -> "Pexp_open"
  | Pexp_letop _ -> "Pexp_letop"
  | Pexp_extension _ -> "Pexp_extension"
  | Pexp_unreachable -> "Pexp_unreachable"

(** env just keeps track of all the bound names *)
let transform_str bound_names (s : structure_item) =
  match s.str_desc with
  | Tstr_value (_rec_flag, vb::_vbs_) ->
    if Option.is_some (Annotation.extract_ignore_attribute vb.vb_attributes) then None
    else
    let tactics = collect_annotations vb.vb_attributes in
    let fn_name = string_of_pattern vb.vb_pat in
    let fn = vb.vb_expr in
    begin match fn.exp_desc with
    | Texp_function (_, _tlbody) ->
      (* see also: CLambda case *)
      let spec = Annotation.extract_spec_attribute vb.vb_attributes |> Option.map Retypehip.retype_staged_spec in
      let formals, body, ((_param_type, return_type) as types) = collect_param_info fn in
      let pure_fn_info =
        let has_pure_annotation =
          List.exists Parsetree.(fun a -> String.equal a.attr_name.txt "pure") vb.vb_attributes
        in
        if has_pure_annotation then Some types else None
      in
      let typed_formals =
        let (types, _) = types in
        List.combine formals types
      in
      let e = transformation (fn_name :: formals @ bound_names) body in
      (* typecheck the specifications *)
      let spec = spec |> Option.map (fun spec ->
        let open Hipprover.Infer_types in
        let spec, _ =
          with_empty_env begin
            with_vartypes (List.to_seq ["res", return_type]) begin
              infer_types_staged_spec spec
            end
          end
        in spec)
      in
      Some (Meth (fn_name, typed_formals, spec, e, tactics, pure_fn_info))
    | Texp_apply _ -> None 
    | _ -> failwith (Format.asprintf "not a function binding: %a" Pprintast.expression (Untypeast.untype_expression fn))
    end
  | Tstr_type (_, {typ_name = {txt = name; _}; typ_params; typ_kind = Ttype_variant _; typ_type; _}::_) ->
      let params = typ_params
        |> List.filter_map (fun (core_type, _) -> match core_type.ctyp_desc with
          | Ttyp_var s -> Some (TVar s)
          | _ -> None
        )
      in
      let constructors = match typ_type.type_kind with
        | Type_variant (variants, _) ->
          let open Compiler_types in
          variants
            |> List.filter_map (fun variant -> match variant.cd_args with
              | Cstr_tuple args -> Some (Ident.name variant.cd_id, List.map hip_type_of_type_expr args)
              | _ -> None)
          
        | _ -> []
      in
      Some (Typedef {tdecl_name = name; tdecl_params = params; tdecl_kind = Tdecl_inductive constructors})
  | Tstr_typext _ -> None 
  | Tstr_primitive { val_name; val_desc; val_prim = [ext_name]; _ } ->
    Globals.using_pure_fns := true;
    let path, name =
      Str.split (Str.regexp "\\.") ext_name |> Utils.Lists.unsnoc
    in
    let rec interpret_arrow_as_params t = match t with
      | Arrow (t1, t2) ->
        let p, r = interpret_arrow_as_params t2 in
        t1 :: p, r
      | _ -> [], t
    in
    let params, ret =
      hip_type_of_type_expr val_desc.ctyp_type |> interpret_arrow_as_params
    in
    Some (LogicTypeDecl (val_name.txt, params, ret, path, name))
  (* TODO we need the full structure to convert s back to a Parsetree.structure via Untypeast *)
  (*| _ -> failwith (Format.asprintf "unknown program element: %a" Pprintast.structure (Untypeast.untype_structure [s]))*)
  | Tstr_open _ | Tstr_attribute _ -> None
  | _ -> failwith "unknown program element"
