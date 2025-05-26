(**
  This version of Core_lang uses Compiler-libs's built in Typedtree instead
  as a basis for transformation.
   *)

open Ocaml_compiler.Ocaml_common
open Typedtree
open Asttypes
(* get rid of the alias *)
type string = label
open Hipcore
open Hiptypes
open Typedhip
open Pretty

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
  | pat -> Format.asprintf "string_of_pattern: %a\n" Pprintast.pattern (Untypeast.untype_pattern p)

let rec hip_type_of_type_expr (texpr: Types.type_expr) =
  match (Types.get_desc texpr) with
  | Tvar (Some var) -> TVar var
  | Tvar (None) -> Typedhip.new_type_var ()
  (* TODO: This does not preserve argument labels, because Heifer's type system does not model them. *)
  | Tarrow (_, t1, t2, _) -> Arrow (hip_type_of_type_expr t1, hip_type_of_type_expr t2)
  (* TODO implement ref types *)
  | Tconstr (path, [], _) -> begin
      match (Path.name path) with
      | "int" -> Int
      | "bool" -> Bool
      | "string" -> TyString
      | "unit" -> Unit
      | unknown -> failwith ("Unknown type constructor: " ^ unknown)
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
        | "^" -> SConcat
        | "+" -> Plus
        | "-" -> Minus
        | _ -> failwith (Format.asprintf "unknown op %s" i)
        end
        in
        BinOp (op, expr_to_term a, expr_to_term b)
    | _ -> failwith (Format.asprintf "unknown term %a" Pprintast.expression (Untypeast.untype_expression expr))
  in
  let term_type = hip_type_of_type_expr expr.exp_type in
  {term_desc; term_type}

(* TODO: expr_to_formula *)
let rec expr_to_formula (expr : expression) : pi * kappa =
  match expr.exp_desc with
  | Texp_apply ({exp_desc = Texp_ident (_, {txt=Lident i; _}, _); }, [(_, Some a); (_, Some b)]) ->
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
      let open Types in
      match (get_desc typ) with
      | Tarrow (_, _, ret, _) -> return_of_arrow_type ret
      | _ -> typ
    in
    (* TODO allow let f : int -> string -> bool = fun a b -> c *)
    let traverse_to_body e =
      match e.exp_desc with
      | Texp_function (params, Tfunction_body body) ->
        let params, param_types = params
          |> List.map (fun param -> param.fp_kind)
          |> List.filter_map (function
              | Tparam_pat pat -> Some (pat.pat_desc, pat.pat_type)
              | _ -> None)
          |> List.filter_map (function
            | (Tpat_var (_, {txt = name; _}, _), typ) -> Some (name, typ)
            | _ -> None)
          |> List.split
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
  | Texp_function (_params, body) ->
    (* see also: Pexp_fun case below in transform_str *)
    let spec = Annotation.extract_spec_attribute expr.exp_attributes in
    (* types aren't used because lambdas cannot be translated to pure functions *)
    let formals, body, (param_types, return_type) = collect_param_info expr in
    let e = transformation (formals @ bound_names) body in
    let bound_vars = List.combine formals param_types
      |> List.map (fun (name, typ) -> binder_of_ident ~typ name) in
    CLambda (bound_vars, Option.map Fill_type.fill_untyped_disj_spec spec, e) |> clang_with_expr_type

  (* shift and shift0 *)
  (*| Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, args) when List.mem name ["shift"; "shift0"] ->*)
  (*  begin match List.map snd args with*)
  (*  | [{pexp_desc = Pexp_ident ({txt = Lident k; _}); _}; body] ->*)
  (*    CShift (name = "shift", k, transformation bound_names body)*)
  (*  | _ ->  failwith "invalid shift args"*)
  (*  end*)
  (*(* reset *)*)
  (*| Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident "reset"; _}, _); _}, args) ->*)
  (*  begin match List.map snd args with*)
  (*  | [body] ->*)
  (*    CReset (transformation bound_names body)*)
  (*  | _ ->  failwith "invalid reset args"*)
  (*  end*)
  (* perform *)
  | Texp_apply ({exp_desc = Texp_ident (_, {txt = Lident name; _}, _); _}, [_, Some {exp_desc=Texp_construct ({txt=Lident eff; _}, _, args); _}]) when name = "!" ->
      begin match args with
      | [a] -> transformation bound_names a |> maybe_var (fun v -> CPerform (eff, Some v) |> clang_with_expr_type)
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
      {core_desc = CValue {term_desc = Const Nil; term_type = exp_hip_type}; core_type = exp_hip_type}
  (* cons *)
  | Texp_construct ({txt = Lident ("::" as name); _}, _, args) ->
    (* this is almost the same as the next case. can't be unified because the pattern has a different type *)
    let rec loop vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars) |> clang_with_expr_type
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
      (* TODO does not properly handle omitted arguments *)
      | (_, Some a) :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop (v :: vars) args1)
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
      CLet ("_", transformation bound_names a, transformation bound_names b) |> clang_with_expr_type
  | Texp_assert (e, _) ->
    let p, k = expr_to_formula e in
    {core_desc = CAssert (p, k); core_type = Unit}
  | Texp_let (_rec, vb::_vbs, e) ->
    let var_name = string_of_pattern (vb.vb_pat) in 
    let exprIn = vb.vb_expr in 
    if String.equal var_name "res" then
      failwith (Format.asprintf "cannot name variable res");
    CLet (var_name, transformation bound_names exprIn, transformation bound_names e) |> clang_with_expr_type 
  | Texp_ifthenelse (if_, then_, Some else_) ->
    let expr = transformation bound_names if_ in 
    (match expr.core_desc with 
    | CValue v -> (CIfElse ((Atomic (EQ, v, true_term)), transformation bound_names then_, transformation bound_names else_)) |> clang_with_expr_type
    | CFunCall (name, [a;b]) -> 
      if String.compare name "==" ==0 then 
        CIfElse ((Atomic (EQ, a, b)), transformation bound_names then_, transformation bound_names else_) |> clang_with_expr_type
      else 
        let v = verifier_getAfreeVar "let" in
        let rest_Expr =  CIfElse ((Atomic (EQ, {term_desc = Var v; term_type = expr.core_type}, true_term)), transformation bound_names then_, transformation bound_names else_) |> clang_with_expr_type in 
        CLet (v, expr, rest_Expr) |> clang_with_expr_type
    | _ -> 
      let v = verifier_getAfreeVar "let" in
      let rest_Expr =  CIfElse ((Atomic (EQ,{term_desc = Var v; term_type = expr.core_type}, true_term)), transformation bound_names then_, transformation bound_names else_) |> clang_with_expr_type in 
      CLet (v, expr, rest_Expr) |> clang_with_expr_type
    )
  | Texp_match (e, computation_cases, value_cases, _) ->
    let effs =
      value_cases |> List.filter_map (fun c ->
        begin match c.c_lhs.pat_desc with
        | Tpat_construct ({txt=Lident eff_name; _}, _, eff_args, _) ->
          let label, arg_binder =
            let arg =
              match eff_args with
              | a::_ -> Some (string_of_pattern a)
              | _ -> None
            in
         eff_name, arg
          in
          let spec = Annotation.extract_spec_attribute c.c_lhs.pat_attributes |> Option.map Fill_type.fill_untyped_disj_spec in
          Some (label, arg_binder, spec, transformation bound_names c.c_rhs)
        | _ -> failwith (Format.asprintf "unknown kind of effect constructor pattern: %a" Pprintast.pattern (Untypeast.untype_pattern c.c_lhs))
        end
      )
    in
    let pattern_cases = 
      computation_cases |> List.filter_map (fun c ->
        match c.c_lhs.pat_desc with
        | Tpat_value value_arg ->
            let pat = (value_arg :> value general_pattern) in 
            let rec transform_pattern pat = match pat.pat_desc with
              | Tpat_construct ({txt=constr; _}, _, args, _) ->
                  let subpatterns = List.map transform_pattern args in
                  if List.exists Option.is_none subpatterns then None
                  else Some (PConstr (String.concat "." (Longident.flatten constr), List.map Option.get subpatterns))
              | Tpat_var (ident, _, _) -> Some (PVar (Ident.name ident, hip_type_of_type_expr pat.pat_type))
              | _ -> None
            in
            Option.map (fun pat -> (pat, transformation bound_names c.c_rhs)) (transform_pattern pat)
        | _ -> None)
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
    let v = verifier_getAfreeVar "let" in
    let let_body = f {term_desc = Var v; term_type = e.core_type} in
    {core_desc = CLet (v, e, let_body); core_type = let_body.core_type}


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
    let tactics = collect_annotations vb.vb_attributes in
    let fn_name = string_of_pattern vb.vb_pat in
    let fn = vb.vb_expr in
    begin match fn.exp_desc with
    | Texp_function (_, tlbody) ->
      (* see also: CLambda case *)
      let spec = Annotation.extract_spec_attribute vb.vb_attributes |> Option.map Fill_type.fill_untyped_disj_spec in
      let formals, body, types = collect_param_info fn in
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
      Some (Meth (fn_name, typed_formals, spec, e, tactics, pure_fn_info))
    | Texp_apply _ -> None 
    | whatever ->
      failwith (Format.asprintf "not a function binding: %a" Pprintast.expression (Untypeast.untype_expression fn))
    end
  | Tstr_type _ 
  | Tstr_typext _ -> None 
  | Tstr_primitive { val_name; val_desc; val_prim = [ext_name]; _ } ->
    Globals.using_pure_fns := true;
    let path, name =
      Str.split (Str.regexp "\\.") ext_name |> unsnoc
    in
    let rec interpret_arrow_as_params t = match t with
      | TyString | Int | Unit | Bool | Lamb | TVar _ -> [], t
      | Arrow (t1, t2) ->
        let p, r = interpret_arrow_as_params t2 in
        t1 :: p, r
    in
    let params, ret =
      hip_type_of_type_expr val_desc.ctyp_type |> interpret_arrow_as_params
    in
    Some (LogicTypeDecl (val_name.txt, params, ret, path, name))
  (* TODO we need the full structure to convert s back to a Parsetree.structure via Untypeast *)
  (*| _ -> failwith (Format.asprintf "unknown program element: %a" Pprintast.structure (Untypeast.untype_structure [s]))*)
  | Tstr_open _ -> None
  | _ -> failwith "unknown program element"
