(* Functions for printing the typed AST. *)

open Hipcore
open Typedhip
open Types
open Utils.Misc
open Utils.Hstdlib

type 'a fmt = Format.formatter -> 'a -> unit

let pp_sep_comma ppf () = Format.fprintf ppf ",@ "
let pp_call_like : 'a. (Format.formatter -> 'a -> unit) -> Format.formatter -> string -> 'a list -> unit = 
    fun pp_arg ppf name args ->
    let open Format in
    fprintf ppf "@[%s(%a)@]"
      name
      (pp_print_list ~pp_sep:pp_sep_comma pp_arg) args

(* we use records-as-objects instead of classes to make it easier
 to dynamically stack modifications *)
type pretty_printer = {
  pp_typ : pretty_printer -> typ fmt;
  pp_binder : pretty_printer -> binder fmt;
  pp_bin_op : pretty_printer -> bin_rel_op fmt;
  pp_bin_term_op : pretty_printer -> bin_term_op fmt;
  pp_constant : pretty_printer -> const fmt;
  pp_lambda_like : pretty_printer -> (binder list * staged_spec option * core_lang option) fmt;
  pp_term : pretty_printer -> term fmt;
  pp_core_lang : pretty_printer -> core_lang fmt;
  pp_staged_spec : pretty_printer -> staged_spec fmt;
  pp_kappa : pretty_printer -> kappa fmt;
  pp_pi : pretty_printer -> pi fmt;
  pp_state : pretty_printer -> state fmt;
  pp_pattern : pretty_printer -> pattern fmt;
}

let default_printer = {
  pp_typ = begin fun self ppf t ->
    let open Types in
    let open Format in
    match t with
    | Any -> pp_print_string ppf "<any>"
    | TyString -> pp_print_string ppf "string"
    | Int -> pp_print_string ppf "int"
    | Unit -> pp_print_string ppf "unit"
    | TConstr (name, args) -> 
        if List.is_empty args
        then pp_print_string ppf name
        else Format.fprintf ppf "(%a) %s"
        (pp_print_list ~pp_sep:pp_sep_comma (self.pp_typ self)) args
        name
    | Bool -> pp_print_string ppf "bool"
    | Lamb -> pp_print_string ppf "lambda"
    | TVar v -> Format.fprintf ppf "'%s" v
    | Arrow (t1, t2) -> Format.fprintf ppf "%a->%a" (self.pp_typ self) t1 (self.pp_typ self) t2
  end;
  pp_binder = begin fun _ ppf binder ->
    Format.pp_print_string ppf (ident_of_binder binder)
  end;
  pp_bin_op = begin 
    fun _ ppf op ->
    let s = match op with
      | GT -> ">"
      | LT -> "<"
      | EQ -> "="
      | GTEQ -> ">="
      | LTEQ -> "<="
    in
    Format.pp_print_string ppf s
  end;
  pp_bin_term_op = begin
    fun _ ppf op -> 
    let s = match op with
      | Plus -> "+"
      | Minus -> "-"
      | SConcat -> "++"
      | TAnd -> "&&"
      | TPower -> "^"
      | TTimes -> "*"
      | TDiv -> "/"
      | TOr -> "||"
      | TCons -> "::"
    in
    Format.pp_print_string ppf s
  end;
  pp_constant = begin
    fun _ ppf c ->
    let open Format in
    match c with
      | ValUnit -> pp_print_string ppf "()"
      | Num n -> pp_print_int ppf n
      | TStr s -> pp_print_string ppf ("\"" ^ s ^ "\"")
      | Nil -> pp_print_string ppf "[]"
      | TTrue -> pp_print_string ppf "true"
      | TFalse -> pp_print_string ppf "false"
  end;
  pp_lambda_like = begin
    fun self ppf (params, spec, body) ->
    let open Format in
    fprintf ppf "(fun %a (*@@ %a @@*) %a)"
      (pp_print_list ~pp_sep:pp_sep_comma (self.pp_binder self)) params
      (pp_print_option (self.pp_staged_spec self)) spec
      (pp_print_option (fun ppf body -> fprintf ppf "-> %a" (self.pp_core_lang self) body)) body
  end;
  pp_term = begin
    fun self ppf t ->
    let open Format in
    match t.term_desc with
      | Const c -> self.pp_constant self ppf c
      | BinOp (op, lhs, rhs) -> fprintf ppf "@[(%a@ %a@ %a)@]" (self.pp_term self) lhs (self.pp_bin_term_op self) op (self.pp_term self) rhs
      | TNot a -> fprintf ppf "not(%a)" (self.pp_term self) a
      | Var str -> pp_print_string ppf str
      | Rel (bop, t1, t2) -> fprintf ppf "@[(%a@ %a@ %a)@]" (self.pp_term self) t1 (self.pp_bin_op self) bop (self.pp_term self) t2
      | Construct (op, args) | TApp (op, args) -> pp_call_like (self.pp_term self) ppf op args
      | TTuple elems
        -> fprintf ppf "(%a)" (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",") (self.pp_term self)) elems
      | TLambda (_, params, spec, body) -> (self.pp_lambda_like self) ppf (params, spec, body)
  end;
  pp_pattern = begin
    fun self ppf pat ->
    match pat.pattern_desc with
    | PAny -> Format.pp_print_string ppf "_"
    | PVar v -> Format.fprintf ppf "@[%s@]" (fst v)
    | PConstr (name, args) -> pp_call_like (self.pp_pattern self) ppf name args
    | PConstant c -> (self.pp_constant self) ppf c
    | PAlias (p, s) -> Format.fprintf ppf "@[%a@ as@ %s@]" (self.pp_pattern self) p s
  end;
  pp_core_lang = begin
    fun self ppf core ->
    let open Format in
    match core.core_desc with
    | CValue v -> fprintf ppf "@[%a@]" (self.pp_term self) v
    | CLet (v, e1, e2) ->
        fprintf ppf "@[let@ %a@ =@ @[< 1>%a@]@;in@ @[< 1>(%a)@]@]"
        (self.pp_binder self) v 
        (self.pp_core_lang self) e1
        (self.pp_core_lang self) e2
    | CSequence (e1, e2) ->
        fprintf ppf "@[%a;@ %a@]"
          (self.pp_core_lang self) e1
          (self.pp_core_lang self) e2
    | CIfElse (pi, t, e) -> fprintf ppf "@[if@ %a@ then@ @[<>%a@]@ else@ @[<>%a@]@]"
        (self.pp_pi self) pi (self.pp_core_lang self) t (self.pp_core_lang self) e
    | CFunCall (f, xs) -> pp_call_like (self.pp_term self) ppf f xs
    | CWrite (v, e) -> fprintf ppf "@[%s@ :=@ %a@]" v (self.pp_term self) e
    | CRef v -> fprintf ppf "@[ref@ %a@]" (self.pp_term self) v
    | CRead v -> fprintf ppf "@[!%s]" v
    | CAssert (p, h) -> fprintf ppf "@[assert@ (@[<>%a@ /\\@ %a@])@]"
      (self.pp_pi self) p (self.pp_kappa self) h
    | CPerform (eff, arg) ->
        fprintf ppf "@[perform@ %s@ %a@]" eff (pp_print_option (self.pp_term self)) arg
    | CMatch (typ, spec, e, hs, cs) ->
        let pp_core_handler_ops =
          let pp_handler ppf (name, v, spec, body) =
            fprintf ppf "|@ %a@ k@ %a@ ->@ %a@]"
            (fun ppf (name, v) -> match v with
              | None -> pp_print_string ppf name
              | Some v -> fprintf ppf "(%s@ %s)" name v) (name, v)
            (pp_print_option (self.pp_staged_spec self)) spec
            (self.pp_core_lang self) body
          in
          pp_print_list pp_handler
        in
        let pp_handler_type ppf h =
          match h with
          | Deep -> pp_print_string ppf "d"
          | Shallow -> pp_print_string ppf "s"
        in
        let pp_constr_case ppf case =
          Format.(fprintf ppf "@[@ |@ %a%a@ ->@ %a@]" 
            (self.pp_pattern self) case.ccase_pat
            (pp_print_option (self.pp_term self)) case.ccase_guard
            (self.pp_core_lang self) case.ccase_expr)
        in
        let pp_constr_cases ppf cases = 
          let open Format in
          pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,") pp_constr_case ppf cases
        in
        let pp_placeholder s = fun ppf _ -> pp_print_string ppf s in
        let pp_try_catch_lemma = pp_placeholder "[try-catch lemma]" in
        fprintf ppf "@[match[%a]@ (%a)@ with@,%a@,%a@,%a@]"
        pp_handler_type typ
        (pp_print_option pp_try_catch_lemma) spec
        (self.pp_core_lang self) e
        pp_core_handler_ops hs
        pp_constr_cases cs
    | CResume args -> fprintf ppf "@[continue@ %a@]" (pp_print_list (self.pp_term self)) args
    | CLambda (xs, spec, e) -> (self.pp_lambda_like self) ppf (xs, spec, Some e)
    | CShift (b, k, e) -> fprintf ppf "@[%s@ %a@ ->@ %a@]"
      (if b then "Shift" else "Shift0")
      (self.pp_binder self) k
      (self.pp_core_lang self) e
    | CReset e -> fprintf ppf "@[@<%a@>@]" (self.pp_core_lang self) e
  end;
  pp_staged_spec = begin
    fun self ppf f ->
    let open Format in
    match f with
    | Exists (v, spec) ->
      fprintf ppf "@[< 1>ex@ %a.@ @[< 1>%a@]@]"
      (self.pp_binder self) v
      (self.pp_staged_spec self) spec
    | ForAll (v, spec) ->
      fprintf ppf "@[< 1>ex@ %a.@ @[< 1>%a@]@]"
      (self.pp_binder self) v
      (self.pp_staged_spec self) spec
    | Require (p, k) ->
      fprintf ppf "@[req@ (@[< 1>%a@ /\\@ %a@])@]"
      (self.pp_pi self) p (self.pp_kappa self) k
    | NormalReturn (p, k) ->
      fprintf ppf "@[ens@ (@[< 1>%a@ /\\@ %a@])@]"
      (self.pp_pi self) p (self.pp_kappa self) k
    | HigherOrder (f, args) -> pp_call_like (self.pp_term self) ppf f args
    | Shift (z, k, spec, _x, _cont) ->
        fprintf ppf "@[%s(@[< 1>%a.@ %a@])@]"
        (if z then "sh" else "sh0")
        (self.pp_binder self) k
        (self.pp_staged_spec self) spec
    | Reset spec ->
        fprintf ppf "@[%s(@[< 1>%a@])@]"
        "rs"
        (self.pp_staged_spec self) spec
    | Sequence (s1, s2) ->
        fprintf ppf "@[< 1>(%a;@ %a)@]"
        (self.pp_staged_spec self) s1
        (self.pp_staged_spec self) s2
    | Bind (v, s1, s2) ->
        fprintf ppf "@[< 1>let@ %a@ =@ @[< 1>%a@]@ in@ @[< 1>(%a)@]@]"
        (self.pp_binder self) v 
        (self.pp_staged_spec self) s1
        (self.pp_staged_spec self) s2
    | Disjunction (s1, s2) ->
        fprintf ppf "@[(%a@ \\/@ %a)@]"
        (self.pp_staged_spec self) s1
        (self.pp_staged_spec self) s2
    (* TODO *)
    | RaisingEff _ -> pp_print_string ppf "[effect stage]"
    | TryCatch _ -> pp_print_string ppf "[trycatch stage]"
  end;
  pp_pi = begin
    fun self ppf p ->
    let open Format in
    match p with
    | True -> fprintf ppf "T"
    | False -> fprintf ppf "F"
    | And (p1, p2) -> fprintf ppf "@[< 1>%a@ /\\@ %a@]"
        (self.pp_pi self) p1 (self.pp_pi self) p2
    | Or (p1, p2) -> fprintf ppf "@[< 1>%a@ \\/@ %a@]"
        (self.pp_pi self) p1 (self.pp_pi self) p2
    | Not p -> fprintf ppf "@[< 1>~(%a)@]"
        (self.pp_pi self) p
    | Imply (p1, p2) -> fprintf ppf "@[< 1>(%a)@]@ =>@ @[<>(%a)@]"
        (self.pp_pi self) p1 (self.pp_pi self) p2
    | Predicate (name, args) -> pp_call_like (self.pp_term self) ppf name args
    | Subsumption (t1, t2) -> fprintf ppf "@[< 1>(%a)@]@ <:@ @[<>(%a)@]"
        (self.pp_term self) t1 (self.pp_term self) t2
    | Atomic (rel, t1, t2) -> fprintf ppf "@[< 1>(%a@ %a@ %a)@]"
      (self.pp_term self) t1 (self.pp_bin_op self) rel (self.pp_term self) t2
  end;
  pp_kappa = begin
    fun self ppf k ->
    let open Format in
    match k with
    | EmptyHeap -> fprintf ppf "emp"
    | PointsTo (loc, t) -> fprintf ppf "@[%s@ ->@ @[< 1>(%a)@]@]" loc (self.pp_term self) t
    | SepConj (k1, k2) -> fprintf ppf "@[< 1>(%a)@]@ *@ @[<>(%a)@]"
      (self.pp_kappa self) k1 (self.pp_kappa self) k2
  end;
  pp_state = begin
    fun self ppf (p, k) ->
    Format.fprintf ppf "(%a@ /\\@ %a)" (self.pp_kappa self) k (self.pp_pi self) p
  end
}

let add_type_annotations (pp : pretty_printer) : pretty_printer =
(* TODO add annotations to terms, patterns, core lang, etc.. *)
  { pp with
    pp_binder = begin
    fun self ppf b ->
      Format.fprintf ppf "(%s : %a)"
      (ident_of_binder b)
      (self.pp_typ self) (type_of_binder b)
    end;
    pp_term = begin
    fun self ppf t ->
      Format.fprintf ppf "%a : %a"
      (pp.pp_term self) t (pp.pp_typ self) t.term_type
    end;}

type config = {
  cfg_print_types : bool;
  cfg_print_spacing : bool
}

let default_config () = {
  cfg_print_types = false;
  cfg_print_spacing = true
}

let set_single_line ?(enabled = true) cfg = {cfg with cfg_print_spacing = not enabled}
let set_types_display ?(enabled = true) cfg = {cfg with cfg_print_types = enabled}

let pp_with_config cfg pp =
  let pp =
    if cfg.cfg_print_types
    then add_type_annotations pp
    else pp
  in
  pp

let with_changed_out_functions ppf wrapper f =
  let out_functions = Format.pp_get_formatter_out_functions ppf () in
  Format.pp_set_formatter_out_functions ppf (wrapper out_functions);
  let result = f ppf in
  Format.pp_set_formatter_out_functions ppf out_functions;
  result

let with_compact_spacing out_functions = 
  Format.{
    out_functions with
    out_newline = ignore;
    out_indent = (fun _ -> out_functions.out_indent 1);
    out_spaces = (fun _ -> out_functions.out_spaces 1);
}

let format_with_config ppf cfg f =
  if cfg.cfg_print_spacing
  then f ppf
  else
    let@ ppf = with_changed_out_functions ppf with_compact_spacing in
    f ppf

(* We define a separate internal module type for printers, so that
   the string_of functions can still derive from [obtain_printers_internal],
   while still exposing only the Printers type and the [obtain_printers] function
   to the outside. *)

module type Printers_internal = sig
  val pp_staged_spec : staged_spec fmt
  val pp_binder : binder fmt
  val pp_typ : typ fmt
  val pp_term : term fmt
  val pp_pi : pi fmt
  val pp_kappa : kappa fmt
  val pp_state : state fmt
  val pp_pattern : pattern fmt
  val pp_core_lang : core_lang fmt
end

module type Printers = sig
  val pp_staged_spec : Format.formatter -> staged_spec -> unit 
end

let cast_from_internal (module M : Printers_internal) : (module Printers) =
  (module struct
    let pp_staged_spec = M.pp_staged_spec
  end)

let obtain_printers_internal cfg : (module Printers_internal) =
  let pp = pp_with_config cfg default_printer in
  (module struct
    let pp_staged_spec ppf f =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_staged_spec pp ppf f
    let pp_binder ppf f =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_binder pp ppf f
    let pp_typ ppf t =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_typ pp ppf t
    let pp_term ppf t =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_term pp ppf t
    let pp_pi ppf p =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_pi pp ppf p
    let pp_kappa ppf k =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_kappa pp ppf k
    let pp_state ppf st =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_state pp ppf st
    let pp_pattern ppf pat =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_pattern pp ppf pat
    let pp_core_lang ppf core =
      let@ ppf = format_with_config ppf cfg in
      pp.pp_core_lang pp ppf core
  end)

let obtain_printers cfg = cast_from_internal (obtain_printers_internal cfg)

module Default_internal = (val obtain_printers_internal (default_config ()) : Printers_internal)
module Default = (val obtain_printers (default_config ()) : Printers)

let string_of_binder ?(config = default_config ()) b =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_binder b

let string_of_type ?(config = default_config ()) t =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_typ t

let string_of_pi ?(config = default_config ()) p =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_pi p

let string_of_kappa ?(config = default_config ()) k =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_kappa k

let string_of_state ?(config = default_config ()) st =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_state st

let string_of_pattern ?(config = default_config ()) pat =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_pattern pat

let string_of_term ?(config = default_config ()) t =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_term t

let string_of_core_lang ?(config = default_config ()) core =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_core_lang core

let string_of_staged_spec ?(config = default_config ()) f =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%a" M.pp_staged_spec f

let string_of_option ?(none = "") some opt =
  match opt with
  | Some v -> some v
  | None -> none

let string_of_list ?(sep=", ") pp elems =
  List.map pp elems |> String.concat sep

let string_of_pred ?(config = default_config ()) pred =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  Format.asprintf "%s(%s)@, =@ %a" pred.p_name (string_of_list (string_of_binder ~config) pred.p_params) M.pp_staged_spec pred.p_body

let string_of_type_declaration ?(config = default_config ()) tdecl =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  let open Format in
  let pp_inductive ppf constrs =
    let pp_constr ppf (name, arg_types) =
      if List.is_empty arg_types
      then fprintf ppf "@[| %s@]" name
      else fprintf ppf "@[| %s of@ %a@]" name
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ * ") M.pp_typ) arg_types
    in
    pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@,") pp_constr ppf constrs
  in
  let pp_record ppf _r = pp_print_string ppf "record" in
  let pp_kind ppf kind =
    match kind with
    | Tdecl_inductive constrs -> pp_inductive ppf constrs
    | Tdecl_record r -> pp_record ppf r
  in
  Format.asprintf "type@ (%s)@ %s@ =@,@[%a@]" (string_of_list (string_of_type ~config) tdecl.tdecl_params)
    tdecl.tdecl_name
    pp_kind tdecl.tdecl_kind
    
let pp_assoc_list pp_key pp_value ppf m =
  let pp_element ppf (k, v) = 
    Format.fprintf ppf "@[%a -> %a@]" pp_key k pp_value v
  in
  Format.fprintf ppf "@[{%a}@]" (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ") pp_element) m

let string_of_abs_env ?(config = default_config ()) abs_env =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  let variable_types = abs_env.vartypes |> SMap.bindings in
  let type_eqs = (TMap.map (fun t -> U.get t) !(abs_env.equalities)) |> TMap.bindings in
  Format.asprintf "@[vars:@ %a,@ eqs:@ %a@]" (pp_assoc_list Format.pp_print_string M.pp_typ) variable_types (pp_assoc_list M.pp_typ M.pp_typ) type_eqs

let%expect_test "syntax of output" =
  let module With_types = (val obtain_printers (default_config () |> set_types_display) : Printers) in
  let module Compact = (val obtain_printers (default_config () |> set_single_line) : Printers) in
  let int_var v = {term_desc = Var v; term_type = Int} in
  let cint c = {term_desc = Const (Num c); term_type = Int} in
  let (+~) a b = {term_desc = BinOp (Plus, a, b); term_type = Int} in
  let (=~) a b = Atomic (EQ, a, b) in
  let f1 = NormalReturn (int_var "res" =~ cint 0, EmptyHeap) in
  Format.printf "%a" With_types.pp_staged_spec f1;
  [%expect {| |}];

  (* f2 can be any output long enough to force default Format behavior to break lines *)
  let to_sum = List.init 20 Fun.id |> List.map cint in
  let f2 = NormalReturn (int_var "res" =~ List.fold_left (+~) (cint 0) to_sum, EmptyHeap) in
  Format.printf "compacted: %a" Compact.pp_staged_spec f2;
  [%expect {| |}];

  let subpat = List.init 40 (Fun.const {pattern_desc = PAny; pattern_type = Int}) in
  let p1 = {pattern_desc = PConstr ("with_lots_of_arguments", subpat); pattern_type = TConstr ("big_type", [])} in
  Format.printf "expanded: %s\ncompacted: %s\n" (string_of_pattern p1) (string_of_pattern ~config:(default_config () |> set_single_line) p1);
  [%expect {| |}];;
