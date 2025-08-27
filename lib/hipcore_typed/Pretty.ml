(* Functions for printing the typed AST. *)

open Hipcore
open Common
open Typedhip
open Types

exception Foo of string

let colours = Pretty.colours

let string_of_type = Pretty.string_of_type

let red = Pretty.red
let green = Pretty.green
let yellow = Pretty.yellow

let string_of_binder ((ident, typ) : binder) =
  Format.sprintf "(%s : %s)" ident (string_of_type typ)
let string_of_constr_call n args =
  match n, args with
  | "[]", _ -> "[]"
  | "::", [a1; a2] -> Format.asprintf "%s :: %s" (string_of_binder a1) (string_of_binder a2)
  | _ -> Format.asprintf "%s(%s)" n (String.concat ", " (List.map string_of_binder args))

let rec string_of_term t : string =
  Pretty.string_of_term (Untypehip.untype_term t)

and string_of_staged_spec s = Pretty.string_of_staged_spec (Untypehip.untype_staged_spec s)

and string_of_kappa (k:kappa) : string =
  match k with
  | EmptyHeap -> "emp"
  | PointsTo  (str, args) -> Format.sprintf "%s->%s" str (List.map string_of_term [args] |> String.concat ", ")
  | SepConj (k1, k2) -> string_of_kappa k1 ^ "*" ^ string_of_kappa k2
  (*| MagicWand (k1, k2) -> "(" ^ string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  ^ ")" *)
  (* | Implication (k1, k2) -> string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  *)

and string_of_state (p, h) : string =
  match h, p with
  | _, True -> string_of_kappa h
  | EmptyHeap, _ -> string_of_pi p
  | _ ->
    Format.asprintf "%s/\\%s" (string_of_kappa h) (string_of_pi p)
    (* Format.asprintf "%s*%s" (string_of_kappa h) (string_of_pi p) *)

and string_of_bin_op op = Pretty.string_of_bin_op op

and string_of_args : 'a. ('a -> string) -> 'a list -> string = Pretty.string_of_args

and string_of_pi pi : string =
  match pi with
  | True -> "T"
  | False -> "F"
  | Atomic (op, t1, t2) -> string_of_term t1 ^ string_of_bin_op op ^ string_of_term t2
  | And   (p1, p2) -> string_of_pi p1 ^ "/\\" ^ string_of_pi p2
  | Or     (p1, p2) -> string_of_pi p1 ^ "\\/" ^ string_of_pi p2
  | Imply  (p1, p2) -> string_of_pi p1 ^ "=>" ^ string_of_pi p2
  | Not    p -> "not(" ^ string_of_pi p ^ ")"
  | Predicate (str, t) -> str ^ "(" ^ (string_of_args string_of_term t) ^ ")"
  | Subsumption (a, b) -> Format.asprintf "%s <: %s" (string_of_term a) (string_of_term b)

and string_of_try_catch_lemma (x:tryCatchLemma) : string =
  let (tcl_head, tcl_handledCont, (*(h_normal, h_ops),*) tcl_summary) = x in
  "TRY "
  ^
  string_of_staged_spec tcl_head

  ^ (match tcl_handledCont with
  | None -> "" | Some conti -> " # " ^ string_of_staged_spec conti)


  ^ " CATCH \n" (*^ string_of_handlingcases (h_normal, h_ops ) *)
  ^ "=> " ^ string_of_staged_spec tcl_summary

and string_of_handler_type (h:handler_type) : string =
    match h with
    | Deep -> "d"
    | Shallow -> "s"

and string_of_core_lang (e:core_lang) :string = Pretty.string_of_core_lang (Untypehip.untype_core_lang e)

let find_rec p_name =
  object(self)
    inherit [_] reduce_spec as super
    method zero = false
    method plus = (||)

    method! visit_HigherOrder _ f a =
      self#plus (f = p_name) (super#visit_HigherOrder () f a)

    method! visit_Atomic () op a b =
      match op with
      | EQ -> (match (a.term_desc, b.term_desc) with
        | (Var x, Var y) -> x = p_name || y = p_name
        | _ -> false)
      | _ -> false
  end

(**********************************************)
let string_of_existentials vs =
  match vs with
  | [] -> ""
  | _ :: _ -> Format.asprintf "ex %s. " (String.concat "," (List.map string_of_binder vs))

let string_of_res b = if b then green "true" else red "false"

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

let string_of_lemma l =
  Format.asprintf "%s: forall %s, %s <: %s" l.l_name (string_of_list string_of_binder l.l_params) (string_of_staged_spec l.l_left) (string_of_staged_spec l.l_right)

(* let string_of_time = string_of_float *)
let string_of_time = Format.asprintf "%.0f"

let string_of_sset s =
  Format.asprintf "{%s}" (String.concat ", " (SSet.elements s))

let string_of_smap pp s =
  Format.asprintf "{%s}" (String.concat ", " (List.map (fun (k, v) -> Format.asprintf "%s -> %s" k (pp v)) (SMap.bindings s)))

let conj xs =
  match xs with
  | [] -> True
  | x :: xs -> List.fold_right (fun c t -> And (c, t)) xs x

let string_of_pure_fn ({ pf_name; pf_params; pf_ret_type; pf_body } : pure_fn_def) : string =
  Format.asprintf "let %s %s : %s = %s" pf_name (String.concat " " (List.map (fun (p, t) -> Format.asprintf "(%s:%s)" p (string_of_type t)) pf_params)) (string_of_type pf_ret_type) (string_of_core_lang pf_body)

let string_of_tmap pp s =
  Format.asprintf "{%s}" (String.concat ", " (List.map (fun (k, v) -> Format.asprintf "%s -> %s" (string_of_type k) (pp v)) (TMap.bindings s)))

let string_of_abs_env t = Pretty.string_of_abs_env t
  (* "<opaque>" *)

let string_of_typ_env t =
  Format.asprintf "%s" (string_of_smap string_of_type t)


let string_of_quantified to_s (vs, e) =
  match vs with
  | [] -> to_s e
  | _ :: _ -> Format.asprintf "ex %s. %s" (String.concat " " vs) (to_s e)

let string_of_instantiations pv kvs =
  List.map (fun (k, v) -> Format.asprintf "%s := %s" k (pv v)) kvs
  |> String.concat ", " |> Format.asprintf "[%s]"

let string_of_bindings = string_of_instantiations

let string_of_meth_def m =
  Format.asprintf "let rec %s %s\n%s=\n%s" m.m_name
    (match m.m_params with | [] -> "()" | _ -> String.concat " " (List.map string_of_binder m.m_params))
    ((match m.m_spec with None -> "" | Some s -> s |> string_of_staged_spec |> (Format.asprintf "(*@@ %s @@*)\n")))
    (string_of_core_lang m.m_body)

let string_of_program (cp:core_program) :string =
  List.map string_of_meth_def cp.cp_methods |> String.concat "\n\n"

let string_of_pattern p = Pretty.string_of_pattern (Untypehip.untype_pattern p)

(* make these declarations available here as well *)
let string_of_type_declaration tdecl = Pretty.string_of_type_declaration tdecl

let string_of_pred pred_def = Pretty.string_of_pred (Untypehip.untype_pred_def pred_def)

let string_of_bin_term_op = Pretty.string_of_bin_term_op

let string_of_constant = Pretty.string_of_constant

module With_types = struct
  let rec string_of_term t : string =
    let term_str = match t.term_desc with
    | Const c -> string_of_constant c
    | BinOp (op, lhs, rhs) -> Format.asprintf "(%s %s %s)" (string_of_term lhs) (string_of_bin_term_op op) (string_of_term rhs)
    | TNot a -> Format.asprintf "not(%s)" (string_of_term a)
    | Var str -> str
    | Rel (bop, t1, t2) ->
      "(" ^ string_of_term t1 ^ (match bop with | EQ -> "==" | _ -> string_of_bin_op bop) ^ string_of_term t2 ^ ")"
    | TApp (op, args) -> Format.asprintf "%s%s" op (string_of_args string_of_term args)
    | Construct (name, args) -> Format.asprintf "%s%s" name (string_of_args string_of_term args)
    | TLambda (_name, params, sp, body) ->
      let body =
        match body with
        | None -> ""
        | Some b -> Format.asprintf "-> %s" (string_of_core_lang b)
      in
      let param_list = params |> List.map string_of_binder |> String.concat " " in
      Format.asprintf "(fun %s (*@@ %s @@*) %s)" param_list (Option.map string_of_staged_spec sp |> Option.value ~default:"") body
    | TTuple nLi ->
      let rec helper li =
        match li with
        | [] -> ""
        | [x] -> string_of_term x
        | x:: xs -> string_of_term x ^","^ helper xs
      in "(" ^ helper nLi ^ ")"
    in
    "(" ^ term_str ^ " : " ^ (string_of_type t.term_type) ^ ")"
  and string_of_pi pi : string =
    match pi with
    | True -> "T"
    | False -> "F"
    | Atomic (op, t1, t2) -> string_of_term t1 ^ string_of_bin_op op ^ string_of_term t2
    | And   (p1, p2) -> string_of_pi p1 ^ "/\\" ^ string_of_pi p2
    | Or     (p1, p2) -> string_of_pi p1 ^ "\\/" ^ string_of_pi p2
    | Imply  (p1, p2) -> string_of_pi p1 ^ "=>" ^ string_of_pi p2
    | Not    p -> "not(" ^ string_of_pi p ^ ")"
    | Predicate (str, t) -> str ^ "(" ^ (string_of_args string_of_term t) ^ ")"
    | Subsumption (a, b) -> Format.asprintf "%s <: %s" (string_of_term a) (string_of_term b)
  and string_of_kappa (k:kappa) : string =
    match k with
    | EmptyHeap -> "emp"
    | PointsTo  (str, args) -> Format.sprintf "%s->%s" str (List.map string_of_term [args] |> String.concat ", ")
    | SepConj (k1, k2) -> string_of_kappa k1 ^ "*" ^ string_of_kappa k2
  and string_of_core_lang e =
    match e.core_desc with
    | CValue v -> string_of_term v
    | CLet (v, e, e1) -> Format.sprintf "let %s = %s in\n%s" (string_of_binder v) (string_of_core_lang e) (string_of_core_lang e1) | CSequence (e1, e2) -> Format.sprintf "%s;\n%s" (string_of_core_lang e1) (string_of_core_lang e2)
    | CIfElse (pi, t, e) -> Format.sprintf "if %s then %s else (%s)" (string_of_pi pi)  (string_of_core_lang t) (string_of_core_lang e)
    | CFunCall (f, [a; b]) when not (Pretty.is_alpha (String.get f 0)) -> Format.sprintf "%s %s %s" (string_of_term a) f (string_of_term b)
    | CFunCall (f, xs) -> Format.sprintf "%s %s" f (List.map string_of_term xs |> String.concat " ")
    | CWrite (v, e) -> Format.sprintf "%s := %s" v (string_of_term e)
    | CRef v -> Format.sprintf "ref %s" (string_of_term v)
    | CRead v -> Format.sprintf "!%s" v
    | CAssert (p, h) -> Format.sprintf "assert (%s && %s)" (string_of_pi p) (string_of_kappa h)
    | CPerform (eff, Some arg) -> Format.sprintf "perform %s %s" eff (string_of_term arg)
    | CPerform (eff, None) -> Format.sprintf "perform %s" eff
    | CMatch (typ, spec, e, hs, cs) -> Format.sprintf "match[%s] %s%s with\n%s%s"
      (string_of_handler_type typ)
      (Option.map string_of_try_catch_lemma spec |> Option.value ~default:"")
      (string_of_core_lang e)
      (match hs with | [] -> "" | _ :: _ -> string_of_core_handler_ops hs ^ "\n")
      (match cs with [] -> "" | _ :: _ -> string_of_constr_cases cs)
    | CResume tList -> Format.sprintf "continue %s" (List.map string_of_term tList |> String.concat " ")
    | CLambda (xs, spec, e) -> Format.sprintf "fun %s%s -> %s" (xs |> List.map string_of_binder |> List.map (fun s -> "(" ^ s ^ ")") |> String.concat " ")
      (match spec with None -> "" | Some ds -> Format.asprintf " (*@@ %s @@*)" (string_of_staged_spec ds)) (string_of_core_lang e)
    | CShift (b, k, e) -> Format.sprintf "Shift%s %s -> %s" (if b then "" else "0") (string_of_binder k) (string_of_core_lang e)
    | CReset (e) -> Format.sprintf "<%s>" (string_of_core_lang e)
  and string_of_constr_cases cs =
    cs
      |> List.map (fun case -> Format.asprintf "| %s%s -> %s"
        (string_of_pattern case.ccase_pat)
        (match case.ccase_guard with
          | None -> ""
          | Some guard -> Format.asprintf " when %s" (string_of_term guard))
        (string_of_core_lang case.ccase_expr))
      |> String.concat "\n"

  and string_of_core_handler_ops hs =
    List.map (fun (name, v, spec, body) ->
      let spec = spec |> Option.map (fun s -> Format.asprintf " (*@@ %s @@*)" (string_of_staged_spec s)) |> Option.value ~default:"" in
      Format.asprintf "| effect %s k%s -> %s"
        (match v with None -> name | Some v -> Format.asprintf "(%s %s)" name v) spec (string_of_core_lang body)) hs |> String.concat "\n"
  and string_of_state (p, h) : string =
    match h, p with
    | _, True -> string_of_kappa h
    | EmptyHeap, _ -> string_of_pi p
    | _ ->
      Format.asprintf "%s/\\%s" (string_of_kappa h) (string_of_pi p)
  and string_of_staged_spec (st:staged_spec) : string =
    match st with
    | Shift (nz, k, spec, x, cont) ->
      (* TODO: shiftc *)
      let zero = if nz then "" else "0" in
      let cont_s = match cont with
        | NormalReturn (Atomic (EQ, {term_desc = Var "res"; _}, {term_desc = Var y; _}), EmptyHeap) when (ident_of_binder x) = y -> ""
        | _ -> Format.asprintf ", %s. %s" (string_of_binder x) (string_of_staged_spec cont)
      in
      Format.asprintf "shift%s(%s. %s%s)" zero (string_of_binder k) (string_of_staged_spec spec) cont_s
    | Reset (spec, x, cont) ->
      (* TODO: resetc *)
      ignore (x, cont);
      Format.asprintf "reset(%s)" (string_of_staged_spec spec)
    | Require (p, h) ->
      Format.asprintf "req %s" (string_of_state (p, h))
    | HigherOrder (f, args) ->
        Format.asprintf "%s(%s)" f (String.concat ", " (List.map string_of_term args))
    | NormalReturn (pi, heap) ->
      Format.asprintf "ens %s" (string_of_state (pi, heap))
    | RaisingEff (pi, heap, (name, args), ret) ->

      Format.asprintf "%s(%s, %s, %s)" name (string_of_state (pi, heap)) (string_of_args string_of_term args) (string_of_term ret)
    | Exists (vs, spec) ->
      Format.asprintf "ex %s. (%s)" (string_of_binder vs) (string_of_staged_spec spec)
    | ForAll (vs, spec) ->
      Format.asprintf "forall %s. (%s)" (string_of_binder vs) (string_of_staged_spec spec)
    (* | IndPred {name; args} -> *)
      (* Format.asprintf "%s(%s)" name (String.concat " " (List.map string_of_term args)) *)
    | TryCatch (pi, h, ( src, ((normP, normSpec), ops)), ret) ->
      let string_of_normal_case = normP ^ ": " ^ string_of_staged_spec (normSpec) in
      let string_of_eff_case (eName, param, eSpec)=  eName  ^
        (match param with | None -> " " | Some p -> "("^ p ^ ") ")^ ": " ^ string_of_staged_spec eSpec   in
      let string_of_eff_cases ops =  List.fold_left (fun acc a -> acc ^ ";\n" ^string_of_eff_case a) "" ops in
      Format.asprintf "ens %s; \n(TRY \n(%s)\nCATCH \n{%s%s}[%s])\n" (string_of_state (pi, h)) (string_of_staged_spec src) (string_of_normal_case) (string_of_eff_cases ops) (string_of_term ret)
    | Sequence (s1, s2) -> Format.sprintf "%s; %s" (string_of_staged_spec s1) (string_of_staged_spec s2)
    | Bind (v, expr, body) -> Format.sprintf "let %s = (%s) in (%s)" (string_of_binder v) (string_of_staged_spec expr) (string_of_staged_spec body)
    | Disjunction (lhs, rhs) -> Format.sprintf "(%s) \\/ (%s)" (string_of_staged_spec lhs) (string_of_staged_spec rhs)
  and string_of_pattern (p : pattern) : string =
    let desc = match p.pattern_desc with
    | PAny -> "_"
    | PVar s -> (ident_of_binder s)
    | PConstr (name, args) -> Format.sprintf "%s(%s)" name (List.map string_of_pattern args |> String.concat ", ")
    | PConstant c -> Format.sprintf "%s" (string_of_constant c)
    | PAlias (p, s) -> Format.sprintf "(%s) as %s" (string_of_pattern p) s
    in
    Format.sprintf "%s : %s" desc (string_of_type p.pattern_type)

  let string_of_pred ({p_name; p_params; p_body; _}) =
    Format.asprintf "%s(%s) == %s" p_name (p_params |> List.map string_of_binder |> String.concat ", ") (string_of_staged_spec p_body)
end

(** formatters, more fit for external output *)

let pp_bin_op ppf op =
  Format.fprintf ppf "%s" (string_of_bin_op op)

let pp_binder ppf (str, typ) =
  Format.fprintf ppf "%s@ :@ %s" str (string_of_type typ)

let pp_bin_term_op ppf op =
  Format.fprintf ppf "%s" (string_of_bin_term_op op)

let pp_constant ppf c =
  Format.fprintf ppf "%s" (string_of_constant c)

let rec pp_term ppf t =
  let open Format in
  match t.term_desc with
  | Const c -> fprintf ppf "%a" pp_constant c
  | BinOp (op, lhs, rhs) -> fprintf ppf "@[<hov 1>(%a@ %a@ %a)@]"
    pp_term lhs pp_bin_term_op op pp_term rhs
  | Rel (op, lhs, rhs) -> fprintf ppf "@[<hov 1>(%a@ %a@ %a)@]"
    pp_term lhs pp_bin_op op pp_term rhs
  | TNot t -> fprintf ppf "@[<hov 1>~(%a)@]" pp_term t
  | Var v -> fprintf ppf "%s" v
  | TApp (op, args) -> pp_call_like pp_term ppf (op, args)
  | Construct (name, args) -> pp_call_like pp_term ppf (name, args)
  | TLambda (_name, params, sp, body) -> pp_lambda_like ppf (params, sp, body)
  (* | TList args ->
      fprintf ppf "[@[<hov 1>%a@]]"
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ";@ ") pp_term) args *)
  | TTuple args ->
      fprintf ppf "(@[<hov 1>%a@])"
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",@ ") pp_term) args
and pp_call_like : 'a. (Format.formatter -> 'a -> unit) -> Format.formatter -> string * 'a list -> unit
  = fun pp_arg ppf (f, args) ->
  let open Format in
    fprintf ppf "@[<hov 1>%s(@[<hov>%a@])@]" f
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",@ ") pp_arg) args
and pp_lambda_like ppf (params, spec, body) =
  let open Format in
  fprintf ppf "@[(fun@ %a@ @[<hov 1>@ (*@@@ %a@ @@*)@ %a@])@]"
    (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",@ ") pp_binder) params
    (pp_print_option pp_staged_spec) spec
    (pp_print_option (fun ppf body -> fprintf ppf "@ ->@ %a" pp_core_lang body)) body
and pp_pi ppf p =
  let open Format in
  match p with
  | True -> fprintf ppf "true"
  | False -> fprintf ppf "false"
  | And (p1, p2) -> fprintf ppf "@[<hov 1>%a@ /\\@ %a@]"
      pp_pi p1 pp_pi p2
  | Or (p1, p2) -> fprintf ppf "@[<hov 1>%a@ \\/@ %a@]"
      pp_pi p1 pp_pi p2
  | Not p -> fprintf ppf "@[<hov 1>~(%a)@]"
      pp_pi p
  | Imply (p1, p2) -> fprintf ppf "@[<hov 1>(%a)@]@ =>@ @[<hov>(%a)@]"
      pp_pi p1 pp_pi p2
  | Predicate (name, args) -> pp_call_like pp_term ppf (name, args)
  | Subsumption (t1, t2) -> fprintf ppf "@[<hov 1>(%a)@]@ <:@ @[<hov>(%a)@]"
      pp_term t1 pp_term t2
  | Atomic (rel, t1, t2) -> fprintf ppf "@[<hov 1>(%a@ %a@ %a)@]"
    pp_term t1 pp_bin_op rel pp_term t2
and pp_kappa ppf k =
  let open Format in
  match k with
  | EmptyHeap -> fprintf ppf "emp"
  | PointsTo (loc, t) -> fprintf ppf "@[%s@ ->@ @[<hov 1>(%a)@]@]" loc pp_term t
  | SepConj (k1, k2) -> fprintf ppf "@[<hov 1>(%a)@]@ *@ @[<hov>(%a)@]"
    pp_kappa k1 pp_kappa k2
and pp_staged_spec ppf spec =
  let open Format in
  match spec with
  | Exists (v, spec) ->
    fprintf ppf "@[<hov 1>ex@ %a.@ @[<hov 1>%a@]@]"
    pp_binder v
    pp_staged_spec spec
  | Require (p, k) ->
    fprintf ppf "@[req@ (@[<hov 1>%a@ /\\@ %a@])@]"
    pp_pi p pp_kappa k
  | NormalReturn (p, k) ->
    fprintf ppf "@[ens@ (@[<hov 1>%a@ /\\@ %a@])@]"
    pp_pi p pp_kappa k
  | HigherOrder (f, args) -> pp_call_like pp_term ppf (f, args)
  | Shift (z, k, spec, _x, _cont) ->
      fprintf ppf "@[%s(@[<hov 1>%a.@ %a@])@]"
      (if z then "sh" else "sh0")
      pp_binder k
      pp_staged_spec spec
  | Reset (spec, _x, _cont) ->
      fprintf ppf "@[%s(@[<hov 1>%a@])@]"
      "rs"
      pp_staged_spec spec
  | Sequence (s1, s2) ->
      fprintf ppf "@[<hov 1>(%a;@ %a)@]"
      pp_staged_spec s1
      pp_staged_spec s2
  | Bind (v, s1, s2) ->
      fprintf ppf "@[<hov 1>let@ %a@ =@ @[<hov 1>%a@]@ in@ @[<hov 1>(%a)@]@]"
      pp_binder v
      pp_staged_spec s1
      pp_staged_spec s2
  | Disjunction (s1, s2) ->
      fprintf ppf "@[(%a@ \\/@ %a@]"
      pp_staged_spec s1
      pp_staged_spec s2
  (* the remaining cases are effect-related, no need to prettify for now *)
| s -> pp_print_string ppf (string_of_staged_spec s)
and pp_try_catch_lemma ppf (head, cont, summary) =
  Format.(fprintf ppf "@[TRY@ %a@ %a@ =>@ %a@]"
    pp_staged_spec head
    (pp_print_option (fun ppf spec -> fprintf ppf "#@ %a" pp_staged_spec spec)) cont
    pp_staged_spec summary)
and pp_pattern ppf pat =
  match pat.pattern_desc with
  | PAny -> Format.pp_print_string ppf "_"
  | PVar v -> Format.fprintf ppf "@[%s@]" (fst v)
  | PConstr (name, args) -> pp_call_like pp_pattern ppf (name, args)
  | PConstant c -> pp_constant ppf c
  | PAlias (p, s) -> Format.fprintf ppf "@[%a@ as@ %s@]" pp_pattern p s
and pp_constr_case ppf case =
  Format.(fprintf ppf "@[@ |@ %a%a@ ->@ %a@]"
    pp_pattern case.ccase_pat
    (pp_print_option pp_term) case.ccase_guard
    pp_core_lang case.ccase_expr)
and pp_constr_cases ppf cases =
  let open Format in
  pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "@,") pp_constr_case ppf cases
and pp_core_lang ppf core =
  let open Format in
  match core.core_desc with
  | CValue v -> fprintf ppf "@[%a@]" pp_term v
  | CLet (v, e1, e2) ->
      fprintf ppf "@[let@ %a@ =@ @[<hov 1>%a@]@;in@ @[<hov 1>(%a)@]@]"
      pp_binder v
      pp_core_lang e1
      pp_core_lang e2
  | CSequence (e1, e2) ->
      fprintf ppf "@[%a;@ %a@]"
        pp_core_lang e1
        pp_core_lang e2
  | CIfElse (pi, t, e) -> fprintf ppf "@[if@ %a@ then@ @[<hov>%a@]@ else@ @[<hov>%a@]@]"
      pp_pi pi pp_core_lang t pp_core_lang e
  | CFunCall (f, xs) -> pp_call_like pp_term ppf (f, xs)
  | CWrite (v, e) -> fprintf ppf "@[%s@ :=@ %a@]" v pp_term e
  | CRef v -> fprintf ppf "@[ref@ %a@]" pp_term v
  | CRead v -> fprintf ppf "@[!%s]" v
  | CAssert (p, h) -> fprintf ppf "@[assert@ (@[<hov>%a@ /\\@ %a@])@]"
    pp_pi p pp_kappa h
  | CPerform (eff, arg) ->
      fprintf ppf "@[perform@ %s@ %a@]" eff (pp_print_option pp_term) arg
  | CMatch (typ, spec, e, hs, cs) ->
      let pp_core_handler_ops =
        let pp_handler ppf (name, v, spec, body) =
          fprintf ppf "|@ %a@ k@ %a@ ->@ %a@]"
          (fun ppf (name, v) -> match v with
            | None -> pp_print_string ppf name
            | Some v -> fprintf ppf "(%s@ %s)" name v) (name, v)
          (pp_print_option pp_staged_spec) spec
          pp_core_lang body
        in
        pp_print_list pp_handler
      in
      fprintf ppf "@[match[%s]@ (%a)@ with@,%a@,%a@,%a@]"
      (string_of_handler_type typ)
      (pp_print_option pp_try_catch_lemma) spec
      pp_core_lang e
      pp_core_handler_ops hs
      pp_constr_cases cs
  | CResume args -> fprintf ppf "@[continue@ %a@]" (pp_print_list pp_term) args
  | CLambda (xs, spec, e) -> pp_lambda_like ppf (xs, spec, Some e)
  | CShift (b, k, e) -> fprintf ppf "@[%s@ %a@ ->@ %a@]"
    (if b then "Shift" else "Shift0")
    pp_binder k
    pp_core_lang e
  | CReset e -> fprintf ppf "@[<%a>@]" pp_core_lang e
