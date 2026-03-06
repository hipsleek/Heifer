open Parsetree
open Asttypes
open Core_lang

let rec string_of_pattern_desc desc : string =
  match desc with
  | Ppat_any -> "_"
  | Ppat_var str -> str.txt
  | Ppat_constant { pconst_desc = Pconst_integer (i, _); _ } -> i
  | Ppat_constant { pconst_desc = Pconst_string (s, _, _); _ } -> s
  | Ppat_construct (l, _) -> List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)
  | _ -> failwith "string_of_pattern_desc: unsupported"

and string_of_pattern p : string = string_of_pattern_desc p.ppat_desc

let preprocess_spec_comments =
  let spec_attr_pattern = {|let \(.+\)\([
 ]*\)(\*@\([^@]+\)@\*)|} in
  let spec_attr_regex = Str.regexp spec_attr_pattern in
  fun text -> Str.global_replace spec_attr_regex "let [@spec {|\\3|}] \\1\\2" text

let extract_spec_attribute attrs =
  List.find_map
    (fun a ->
      if String.equal a.attr_name.txt "spec" then
        match a.attr_payload with
        | PStr
            [
              {
                pstr_desc =
                  Pstr_eval
                    ( { pexp_desc = Pexp_constant { pconst_desc = Pconst_string (s, _, _); _ }; _ },
                      _ );
                _;
              };
            ] -> Some s
        | _ -> None
      else None)
    attrs

let rec pat_to_core_lang_pat pat =
  match pat.ppat_desc with
  | Ppat_any -> PAny
  | Ppat_var { txt = x; _ } -> PVar x
  | Ppat_construct ({ txt = c; _ }, None) -> PConstr (Longident.last c, [])
  | Ppat_construct ({ txt = c; _ }, Some ([], { ppat_desc = Ppat_tuple args; _ })) ->
      PConstr (Longident.last c, List.map pat_to_core_lang_pat args)
  | Ppat_construct ({ txt = c; _ }, Some ([], arg)) ->
      PConstr (Longident.last c, [pat_to_core_lang_pat arg])
  | Ppat_constant { pconst_desc = Pconst_integer (i, _); _ } -> PInt (int_of_string i)
  | _ -> failwith (Format.asprintf "Unsupported pattern %a" Pprintast.pattern pat)

let rec expr_to_term (expr : expression) : expr =
  let term =
    match expr.pexp_desc with
    | Pexp_ident { txt = Lident i; _ } -> Var i
    | Pexp_constant { pconst_desc = c; _ } -> begin
        match c with
        | Pconst_integer (i, _) -> Int (int_of_string i)
        | _ -> failwith "unsupported constant"
      end
    | Pexp_let (_rec, vbs, e) ->
        let rec chain_vbs = function
          | [] -> expr_to_term e
          | vb :: rest ->
              let var_name = string_of_pattern vb.pvb_pat in
              let expr_in = expr_to_term vb.pvb_expr in
              let expr_in_with_spec =
                match extract_spec_attribute vb.pvb_attributes with
                | Some s -> WithSpec (expr_in, s, var_name)
                | None -> expr_in
              in
              Let (var_name, expr_in_with_spec, chain_vbs rest)
        in
        chain_vbs vbs
    | Pexp_function (params, _constraint, body) ->
        let names =
          List.filter_map
            (fun p ->
              match p.pparam_desc with
              | Pparam_val (Nolabel, None, pat) -> Some (string_of_pattern pat)
              | _ -> None)
            params
        in
        let body_term =
          match body with
          | Pfunction_body e -> expr_to_term e
          | Pfunction_cases _ -> failwith "function cases not supported"
        in
        Fun (names, body_term)
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident name; _ }; _ }, args)
      when List.mem name ["shift"; "shift0"] -> begin
        match List.map snd args with
        | [{ pexp_desc = Pexp_ident { txt = Lident k; _ }; _ }; body] -> Shift (k, expr_to_term body)
        | _ -> failwith "invalid shift args"
      end
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident "reset"; _ }; _ }, args) -> begin
        match List.map snd args with
        | [body] -> Reset (expr_to_term body)
        | _ -> failwith "invalid reset args"
      end
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident "perform"; _ }; _ }, args) -> begin
        match args with
        | [(_, { pexp_desc = Pexp_construct ({ txt = Lident eff; _ }, arg_opt); _ })] ->
            Perform (eff, Option.map expr_to_term arg_opt)
        | _ -> failwith "invalid perform args"
      end
    | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident name; _ }; _ }, args)
      when name = "continue" || name = "resume" ->
        Resume (List.map (fun (_, a) -> expr_to_term a) args)
    | Pexp_apply (f, args) ->
        let f_term = expr_to_term f in
        let args_term = List.map (fun (_, a) -> expr_to_term a) args in
        Apply (f_term, args_term)
    | Pexp_ifthenelse (if_, then_, Some else_) ->
        If (expr_to_term if_, expr_to_term then_, expr_to_term else_)
    | Pexp_sequence (a, b) -> Sequence (expr_to_term a, expr_to_term b)
    | Pexp_match (e, cases) ->
        let e_term = expr_to_term e in
        let cases_term =
          List.map
            (fun c ->
              if Option.is_some c.pc_guard then failwith "match guard not supported";
              (pat_to_core_lang_pat c.pc_lhs, expr_to_term c.pc_rhs))
            cases
        in
        Match (e_term, cases_term)
    | _ ->
        failwith (Format.asprintf "expression not in core language: %a" Pprintast.expression expr)
  in
  match extract_spec_attribute expr.pexp_attributes with
  | Some s -> WithSpec (term, s, "")
  | None -> term

let transform_str (s : structure_item) : (string * expr * bool) option =
  match s.pstr_desc with
  | Pstr_value (_rec_flag, [vb]) ->
      let fn_name = string_of_pattern vb.pvb_pat in
      let fn = vb.pvb_expr in
      let body = expr_to_term fn in
      let is_pure = List.exists (fun a -> String.equal a.attr_name.txt "pure") vb.pvb_attributes in
      let body_with_spec =
        match extract_spec_attribute vb.pvb_attributes with
        | Some s -> WithSpec (body, s, fn_name)
        | None -> body
      in
      Some (fn_name, body_with_spec, is_pure)
  | Pstr_eval (e, _) -> Some ("()", expr_to_term e, false)
  | _ -> None

let process_ocaml_structure (items : structure) : verification_unit =
  let rec loop pure_acc prog_acc items =
    match items with
    | [] -> { pure_functions = List.rev pure_acc; program_functions = List.rev prog_acc }
    | item :: rest ->
        (match transform_str item with
        | Some (name, body, true) -> loop ((name, body) :: pure_acc) prog_acc rest
        | Some (name, body, false) -> loop pure_acc ((name, body) :: prog_acc) rest
        | None -> loop pure_acc prog_acc rest)
  in
  loop [] [] items

let parse_ocaml s : verification_unit =
  try
    let s = preprocess_spec_comments s in
    let items = Parse.implementation (Lexing.from_string s) in
    process_ocaml_structure items
  with exn ->
    let bt = Printexc.get_raw_backtrace () in
    Format.printf "%a\n" Location.report_exception exn;
    Printexc.raise_with_backtrace exn bt
