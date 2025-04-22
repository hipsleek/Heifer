
module Hipsubst = Subst
open Ocaml_compiler.Ocaml_common
open Parsetree
open Asttypes
(* get rid of the alias *)
type string = label
open Hipcore
open Hiptypes
open Pretty

exception Foo of string

let rec get_tactic e =
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
  List.fold_right
    (fun c t ->
      match c.attr_payload with
      | PStr [{ pstr_desc = Pstr_eval (e, _); _ }] when String.equal "proof" c.attr_name.txt -> get_tactic e
      | _ -> t)
    attrs []

let string_of_p_constant con : string =
  match con with 
  | Pconst_char i -> String.make 1 i
  | Pconst_string (i, _, None) -> i
  | Pconst_string (i, _, Some delim) -> i ^ delim
  | Pconst_integer (i, None) -> i
  | _ -> "string_of_p_constant"

let string_of_arg_label a = 
  match a with 
  | Nolabel -> ""
  | Labelled str -> str (*  label:T -> ... *)
  | Optional str -> "?" ^ str (* ?label:T -> ... *)

let rec string_of_core_type (p:core_type) :string =
  match p.ptyp_desc with 
  | Ptyp_any -> "_"
  | Ptyp_var str -> str
  | Ptyp_arrow (a, c1, c2) -> string_of_arg_label a ^  string_of_core_type c1 ^ " -> " ^ string_of_core_type c2 ^"\n"
  | Ptyp_constr (l, c_li) -> 
    List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)^
    List.fold_left (fun acc a -> acc ^ string_of_core_type a) "" c_li
  | Ptyp_tuple (ctLi) -> "(" ^
    (List.fold_left (fun acc a -> acc ^ "," ^ string_of_core_type a ) "" ctLi) ^ ")"

  | Ptyp_poly (str_li, c) -> 
    "type " ^ List.fold_left (fun acc a -> acc ^ a.txt) "" str_li ^ ". " ^
    string_of_core_type c 


  | _ -> "\nlsllsls\n"
let rec string_of_pattern (p) : string = 
  match p.ppat_desc with 
  | Ppat_any -> "_"
  (* _ *)
  | Ppat_var str -> str.txt
  (* x *)
  | Ppat_constant {pconst_desc = con; _} -> string_of_p_constant con
  | Ppat_type l -> List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)
  | Ppat_constraint (p1, c) -> string_of_pattern p1 ^ " : "^ string_of_core_type c
  (* (P : T) *)
  | Ppat_effect (p1, p2) -> string_of_pattern p1 ^ string_of_pattern p2 ^ "\n"

  | Ppat_construct (l, None) -> List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)
  | Ppat_construct (l, Some _p1) ->  
    List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)
    (* ^ string_of_pattern p1 *)
  (* #tconst *)

  
  | _ -> Format.asprintf "string_of_pattern: %a\n" Pprintast.pattern p;;
let rec expr_to_term (expr:expression) : term =
  match expr.pexp_desc with
  | Pexp_constant {pconst_desc = Pconst_integer (i, _); _} -> Num (int_of_string i)
  | Pexp_ident {txt=Lident i; _} -> Var i
  | Pexp_apply ({pexp_desc = Pexp_ident {txt=Lident i; _}; _}, [(_, a); (_, b)]) ->
      begin match i with
      | "^" -> SConcat (expr_to_term a, expr_to_term b)
      | "+" -> Plus (expr_to_term a, expr_to_term b)
      | "-" -> Minus (expr_to_term a, expr_to_term b)
      | _ -> failwith (Format.asprintf "unknown op %s" i)
      end
  | _ -> failwith (Format.asprintf "unknown term %a" Pprintast.expression expr)

let rec expr_to_formula (expr:expression) : pi * kappa =
  match expr.pexp_desc with
  | Pexp_apply ({pexp_desc = Pexp_ident {txt=Lident i; _}; _}, [(_, a); (_, b)]) ->
      begin match i with
      | "=" ->
        (* !i=a is allowed as shorthand for i-->a, but equalities between pointer values, e.g. !i=!j, are not generally allowed. they can be expressed using let v=!i in assert (!j=v). *)
        begin match a.pexp_desc, b.pexp_desc with
        | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident "!"; _}); _}, [_, {pexp_desc = Pexp_ident {txt=Lident p; _}; _}]), _ ->
          True, PointsTo (p, expr_to_term b)
        | _ ->
          Atomic (EQ, expr_to_term a, expr_to_term b), EmptyHeap
        end
      | "<" -> Atomic (LT, expr_to_term a, expr_to_term b), EmptyHeap
      | "<=" -> Atomic (LTEQ, expr_to_term a, expr_to_term b), EmptyHeap
      | ">" -> Atomic (GT, expr_to_term a, expr_to_term b), EmptyHeap
      | ">=" -> Atomic (GTEQ, expr_to_term a, expr_to_term b), EmptyHeap
      | "&&" ->
        let p1, h1 = expr_to_formula a in
        let p2, h2 = expr_to_formula b in
        And (p1, p2), SepConj (h1, h2)
      | "=>" ->
        let p1, _h1 = expr_to_formula a in
        let p2, _h2 = expr_to_formula b in
        Imply (p1, p2), EmptyHeap (* no magic wand *)
      | "||" ->
        let p1, _h1 = expr_to_formula a in
        let p2, _h2 = expr_to_formula b in
        Or (p1, p2), EmptyHeap (* heap disjunction is not possible *)
      | "-->" ->
        let v =
          match expr_to_term a with
          | Var s -> s
          | _ -> failwith (Format.asprintf "invalid lhs of points to: %a" Pprintast.expression a)
        in
        True, PointsTo (v, expr_to_term b)
      | _ ->
        failwith (Format.asprintf "unknown binary op: %s" i)
      end
  | Pexp_apply ({pexp_desc = Pexp_ident {txt=Lident i; _}; _}, [(_, _a)]) ->
      begin match i with
      (* | "not" -> Not (expr_to_formula a) *)
      | _ -> failwith (Format.asprintf "unknown unary op: %s" i)
      end
  | Pexp_construct ({txt=Lident "true"; _}, None) -> True, EmptyHeap
  | Pexp_construct ({txt=Lident "false"; _}, None) -> False, EmptyHeap
  | _ ->
    failwith (Format.asprintf "unknown kind of formula: %a" Pprintast.expression expr)

let rec core_type_to_simple_type t =
  match t.ptyp_desc with
  | Ptyp_constr ({txt = Lident "bool"; _}, []) -> Bool
  | Ptyp_constr ({txt = Lident "int"; _}, []) -> Int
  | Ptyp_constr ({txt = Lident "list"; _}, [
    { ptyp_desc = Ptyp_constr ({txt = Lident "int"; _}, []) ; _}
  ]) -> List_int
  | Ptyp_arrow (_, t1, t2) -> Arrow (core_type_to_simple_type t1, core_type_to_simple_type t2)
  | _ -> failwith (Format.asprintf "core_type_to_simple_type: not yet implemented %a" Pprintast.core_type t)

(** Given the RHS of a let binding, returns the es it is annotated with *)
let function_spec _rhs =
  (* FIXME Implement reading this in via attributes. *)
  None

(*
   let f (a:int) (b:string) : bool = c

   is actually

   let f = fun (a:int) -> fun (b:string) -> (c:bool)

   This recurses down the funs non-tail-recursively to collect all variable names, their types, the return type, and the body.
*)
let collect_param_info rhs =
    (* TODO allow let f : int -> string -> bool = fun a b -> c *)
    let traverse_to_body e ret_type =
      match e.pexp_desc with
      | Pexp_function (params, ret_type, Pfunction_body body) ->
        let params, types = params
          |> List.map (fun param -> param.pparam_desc)
          |> List.filter_map (function
              | Pparam_val (_, _, pat) -> Some pat.ppat_desc
              | _ -> None)
          |> List.filter_map (function
            | Ppat_constraint ({ppat_desc = Ppat_var {txt = name; _}; _}, t) -> Some (name, Some (core_type_to_simple_type t))
            | Ppat_var {txt = name; _} -> Some (name, None)
            | _ -> None)
          |> List.split
        in
        let ret_type = ret_type |> Option.map (fun ret_type -> match ret_type with
        | Pconstraint t 
        | Pcoerce (_, t) -> core_type_to_simple_type t)
        in
        let func_type = 
          if List.for_all Option.is_some types && Option.is_some ret_type
          then
            Some (types |> List.map Option.get, Option.get ret_type)
          else None
        in
        (params, body, func_type)
      | _ ->
        (* we have reached the end *)
        ([], e, ret_type)
    in
    let names, body, types = traverse_to_body rhs None in
    names, body, types

let rec transformation (bound_names:string list) (expr:expression) : core_lang =
  match expr.pexp_desc with 
  | Pexp_ident {txt=Lident i; _} ->
    CValue (Var i)
  | Pexp_construct ({txt=Lident "true"; _}, None) ->
    CValue TTrue
  | Pexp_construct ({txt=Lident "false"; _}, None) ->
    CValue TFalse
  | Pexp_construct ({txt=Lident "()"; _}, None) ->
    CValue (UNIT)
  | Pexp_constant {pconst_desc = c; _} ->
    begin match c with
    | Pconst_integer (i, _) -> CValue (Num (int_of_string i))
    | Pconst_string (s, _, _) -> CValue (TStr s)
    | _ -> failwith (Format.asprintf "unknown kind of constant: %a" Pprintast.expression expr)
    end
  (* lambda *)
  | Pexp_function (_, _, body) ->
    (* see also: Pexp_fun case below in transform_str *)
    let spec = function_spec body in
    (* types aren't used because lambdas cannot be translated to pure functions *)
    let formals, body, _types = collect_param_info expr in
    let e = transformation (formals @ bound_names) body in
    CLambda (formals, spec, e)
  (* shift and shift0 *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, args) when List.mem name ["shift"; "shift0"] ->
    begin match List.map snd args with
    | [{pexp_desc = Pexp_ident ({txt = Lident k; _}); _}; body] ->
      CShift (name = "shift", k, transformation bound_names body)
    | _ ->  failwith "invalid shift args"
    end
  (* reset *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident "reset"; _}); _}, args) ->
    begin match List.map snd args with
    | [body] ->
      CReset (transformation bound_names body)
    | _ ->  failwith "invalid reset args"
    end
  (* perform *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, ((_, {pexp_desc = Pexp_construct ({txt=Lident eff; _}, args); _}) :: _)) when name = "perform" ->
    begin match args with
    | Some a -> transformation bound_names a |> maybe_var (fun v -> CPerform (eff, Some v))
    | None -> CPerform (eff, None)
    end
  (* continue *)
  (*| Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, _k; _, e]) when name = "continue" ->
    transformation env e |> maybe_var (fun v -> CResume v)
  *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, args) when name = "continue" || name = "resume" ->
    (*print_endline (List.fold_left  (fun acc a -> acc ^ ", " ^ a) "" bound_names); *)
    let rec loop vars args =
      match args with
      | [] -> CResume (List.rev vars)
      | (_, a) :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  
  (* dereference *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, {pexp_desc=Pexp_ident {txt=Lident v;_}; _}]) when name = "!" ->
    CRead v
  (* ref *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, a]) when name = "ref" ->
    transformation bound_names a |> maybe_var (fun v -> CRef v)
  (* assign *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, {pexp_desc = Pexp_ident {txt=Lident x; _}; _}; _, e]) when name = ":=" ->
    transformation bound_names e |> maybe_var (fun v -> CWrite (x, v))
  (* transparent *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Ldot (Lident "Sys", "opaque_identity"); _}); _}, [_, a]) ->
    (* ignore this *)
    transformation bound_names a
  (* primitive or invocation of higher-order function passed as argument *)
  | Pexp_construct ({txt=Lident "[]"; _}, None) ->
    CValue Nil
  | Pexp_construct ({txt=Lident ("::" as name); _}, Some ({pexp_desc = Pexp_tuple args; _})) ->
    (* this is almost the same as the next case. can't be unified because the pattern has a different type *)
    let rec loop vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars)
      |  a :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, args) when List.mem name bound_names || List.mem name primitive_functions ->
    (* TODO this doesn't model ocaml's right-to-left evaluation order *)
    let rec loop vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars)
      | (_, a) :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  | Pexp_apply (f, args) ->
    (* handles both named/unknown function calls, e.g. printf, and applications of compound expressions, which get named *)
    let rec loop name vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars)
      | (_, a) :: args1 ->
        transformation bound_names a |> maybe_var (fun v -> loop name (v :: vars) args1)
    in
    transformation bound_names f |> maybe_var (fun f1 ->
      match f1 with
      | Var f2 -> loop f2 [] args
      | _ -> failwith "attempt to apply non-function?")
  | Pexp_sequence (a, b) ->
    CLet ("_", transformation bound_names a, transformation bound_names b)
  | Pexp_assert e ->
    let p, k = expr_to_formula e in
    CAssert (p, k)
  | Pexp_let (_rec, vb::_vbs, e) ->
    let var_name = string_of_pattern (vb.pvb_pat) in 
    let exprIn = vb.pvb_expr in 
    if String.equal var_name "res" then
      failwith (Format.asprintf "cannot name variable res");
    CLet (var_name, transformation bound_names exprIn, transformation bound_names e)
  | Pexp_ifthenelse (if_, then_, Some else_) ->
    let expr = transformation bound_names if_ in 
    

    (match expr with 
    | CValue v -> CIfELse ((Atomic (EQ, v, TTrue)), transformation bound_names then_, transformation bound_names else_)
    | CFunCall (name, [a;b]) -> 
      if String.compare name "==" ==0 then 
        CIfELse ((Atomic (EQ, a, b)), transformation bound_names then_, transformation bound_names else_)
        
      else 
        let v = verifier_getAfreeVar "let" in
        let rest_Expr =  CIfELse ((Atomic (EQ, Var v, TTrue)), transformation bound_names then_, transformation bound_names else_) in 
        CLet (v, expr, rest_Expr)

        
    | _ -> 
      let v = verifier_getAfreeVar "let" in
      let rest_Expr =  CIfELse ((Atomic (EQ,Var v, TTrue)), transformation bound_names then_, transformation bound_names else_) in 
      CLet (v, expr, rest_Expr)
    )
      
  | Pexp_match (e, cases) ->
    let norm =
      (* may be none for non-effect pattern matches *)
      cases |> List.find_map (fun c ->
        match c.pc_lhs.ppat_desc with
        | Ppat_var {txt=v; _} -> Some (v, transformation bound_names c.pc_rhs)
        | _ -> None)
    in
    let effs =
      (* may be empty for non-effect pattern matches *)
      cases |> List.filter_map (fun c ->
        match c.pc_lhs.ppat_desc with
        | Ppat_effect (peff, _pk) ->
          let label, arg_binder =
            let arg =
              match peff with
              | {ppat_desc = Ppat_construct (_name, Some (_, a)); _} -> Some (string_of_pattern a)
              | {ppat_desc = Ppat_construct (_name, None); _} -> None
              | _ -> failwith (Format.asprintf "unknown kind of effect constructor pattern: %a" Pprintast.pattern peff)
            in
            string_of_pattern peff, arg
          in
          (* FIXME pass handler specifications in here *)
          Some (label, arg_binder, None, transformation bound_names c.pc_rhs)
        | _ -> None)
    in
    let pattern_cases =
      (* may be empty for non-effect pattern matches *)
      cases |> List.filter_map (fun c ->
        match c.pc_lhs.ppat_desc with
        | Ppat_construct ({txt=constr; _}, None) ->
          Some (Longident.last constr, [], transformation bound_names c.pc_rhs)
        | Ppat_construct ({txt=constr; _}, Some (_, {ppat_desc = Ppat_tuple ps; _})) ->
          let args = List.filter_map (fun p ->
            match p.ppat_desc with
            | Ppat_var {txt=v; _} -> Some v
            | _ -> None) ps
          in
          Some (Longident.last constr, args, transformation bound_names c.pc_rhs)
        | _ -> None)
    in
    (* FIXME properly fill in the handler type and handler specification *)
    CMatch (Shallow, None, transformation bound_names e, norm, effs, pattern_cases)
  | _ -> 
    if String.compare (Pprintast.string_of_expression expr) "Obj.clone_continuation k" == 0 then (* ASK Darius*)
    CValue (Var "k")
    else 
    CValue (UNIT)
    (* failwith (Format.asprintf "expression not in core language: %a" Pprintast.expression expr)  *)
    (* (Format.printf "expression not in core language: %a@." (Printast.expression 0) expr; failwith "failed") *)

and maybe_var f e =
  (* generate fewer unnecessary variables *)
  match e with
  | CValue v -> f v
  | _ ->
    let v = verifier_getAfreeVar "let" in
    CLet (v, e, f (Var v))

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
  match s.pstr_desc with
  | Pstr_value (_rec_flag, vb::_vbs_) ->
    let tactics = collect_annotations vb.pvb_attributes in
    let fn_name = string_of_pattern vb.pvb_pat in
    let fn = vb.pvb_expr in
    begin match fn.pexp_desc with
    | Pexp_function (_, _, tlbody) ->
      (* see also: CLambda case *)
      let spec = function_spec tlbody in
      let formals, body, types = collect_param_info fn in
      let pure_fn_info =
        let has_pure_annotation =
          List.exists (fun a -> String.equal a.attr_name.txt "pure") vb.pvb_attributes
        in
        match has_pure_annotation, types with
        | true, None -> failwith (Format.asprintf "%s has pure annotation but no type information given" fn_name)
        | true, Some _ -> types
        | false, _ -> None
      in
      let e = transformation (fn_name :: formals @ bound_names) body in
      Some (Meth (fn_name, formals, spec, e, tactics, pure_fn_info))
    | Pexp_apply _ -> None 
    | whatever ->
      print_endline (string_of_expression_kind whatever); 
      failwith (Format.asprintf "not a function binding: %a" Pprintast.expression fn)
    end
  | Pstr_type _ 
  | Pstr_typext _ -> None 
  | Pstr_primitive { pval_name; pval_type; pval_prim = [ext_name]; _ } ->
    Globals.using_pure_fns := true;
    let path, name =
      Str.split (Str.regexp "\\.") ext_name |> unsnoc
    in
    let params, ret =
      core_type_to_simple_type pval_type |> Subst.interpret_arrow_as_params
    in
    Some (LogicTypeDecl (pval_name.txt, params, ret, path, name))
  | _ -> failwith (Format.asprintf "unknown program element: %a" Pprintast.structure [s])
