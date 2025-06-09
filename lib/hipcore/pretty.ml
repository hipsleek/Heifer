(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open Hiptypes

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

exception Foo of string


let colours : [`Html|`Ansi|`None] ref = ref `None

let col ~ansi ~html text =
  (match !colours with
  | `None -> ""
  | `Ansi -> ansi
  | `Html -> html) ^ text ^
  (match !colours with
  | `None -> ""
  | `Ansi -> "\u{001b}[0m"
  | `Html -> "</span>")

let red text = col ~ansi:"\u{001b}[31m" ~html:"<span class=\"output-error\">" text
let green text = col ~ansi:"\u{001b}[32m" ~html:"<span class=\"output-ok\">" text
let yellow text = col ~ansi:"\u{001b}[33m" ~html:"<span class=\"output-emph\">" text

let end_of_var = Str.regexp "_?[0-9]+$"

(*
let string_of_token =
  let open Parser in
  function
| AMPERAMPER -> "AMPERAMPER"
| AMPERSAND -> "AMPERSAND"
| AND -> "AND"
| AS -> "AS"
| ASSERT -> "ASSERT"
| BACKQUOTE -> "BACKQUOTE"
| BANG -> "BANG"
| BAR -> "BAR"
| BARBAR -> "BARBAR"
| BARRBRACKET -> "BARRBRACKET"
| BEGIN -> "BEGIN"
| CHAR _ -> "CHAR"
| CLASS -> "CLASS"
| COLON -> "COLON"
| COLONCOLON -> "COLONCOLON"
| COLONEQUAL -> "COLONEQUAL"
| COLONGREATER -> "COLONGREATER"
| COMMA -> "COMMA"
| CONSTRAINT -> "CONSTRAINT"
| DO -> "DO"
| DONE -> "DONE"
| DOT -> "DOT"
| DOTDOT -> "DOTDOT"
| DOWNTO -> "DOWNTO"
| EFFECT -> "EFFECT"
| ELSE -> "ELSE"
| END -> "END"
| EOF -> "EOF"
| EQUAL -> "EQUAL"
| EXCEPTION -> "EXCEPTION"
| EXTERNAL -> "EXTERNAL"
| FALSE -> "FALSE"
| FLOAT _ -> "FLOAT"
| FOR -> "FOR"
| FUN -> "FUN"
| FUNCTION -> "FUNCTION"
| FUNCTOR -> "FUNCTOR"
| GREATER -> "GREATER"
| GREATERRBRACE -> "GREATERRBRACE"
| GREATERRBRACKET -> "GREATERRBRACKET"
| IF -> "IF"
| IN -> "IN"
| INCLUDE -> "INCLUDE"
| INFIXOP0 _ -> "INFIXOP0"
| INFIXOP1 _ -> "INFIXOP1"
| INFIXOP2 _ -> "INFIXOP2"
| INFIXOP3 _ -> "INFIXOP3"
| INFIXOP4 _ -> "INFIXOP4"
| DOTOP _ -> "DOTOP"
| LETOP _ -> "LETOP"
| ANDOP _ -> "ANDOP"
| INHERIT -> "INHERIT"
| INITIALIZER -> "INITIALIZER"
| INT _ -> "INT"
| LABEL _ -> "LABEL"
| LAZY -> "LAZY"
| LBRACE -> "LBRACE"
| LBRACELESS -> "LBRACELESS"
| LBRACKET -> "LBRACKET"
| LBRACKETBAR -> "LBRACKETBAR"
| LBRACKETLESS -> "LBRACKETLESS"
| LBRACKETGREATER -> "LBRACKETGREATER"
| LBRACKETPERCENT -> "LBRACKETPERCENT"
| LBRACKETPERCENTPERCENT -> "LBRACKETPERCENTPERCENT"
| LESS -> "LESS"
| LESSMINUS -> "LESSMINUS"
| LET -> "LET"
| LIDENT _ -> "LIDENT"
| LPAREN -> "LPAREN"
| LBRACKETAT -> "LBRACKETAT"
| LBRACKETATAT -> "LBRACKETATAT"
| LBRACKETATATAT -> "LBRACKETATATAT"
| MATCH -> "MATCH"
| METHOD -> "METHOD"
| MINUS -> "MINUS"
| MINUSDOT -> "MINUSDOT"
| MINUSGREATER -> "MINUSGREATER"
| MODULE -> "MODULE"
| MUTABLE -> "MUTABLE"
| NEW -> "NEW"
| NONREC -> "NONREC"
| OBJECT -> "OBJECT"
| OF -> "OF"
| OPEN -> "OPEN"
| OPTLABEL _ -> "OPTLABEL"
| OR -> "OR"
| PERCENT -> "PERCENT"
| PLUS -> "PLUS"
| PLUSDOT -> "PLUSDOT"
| PLUSEQ -> "PLUSEQ"
| PREFIXOP _ -> "PREFIXOP"
| PRIVATE -> "PRIVATE"
| QUESTION -> "QUESTION"
| QUOTE -> "QUOTE"
| RBRACE -> "RBRACE"
| RBRACKET -> "RBRACKET"
| REC -> "REC"
| RPAREN -> "RPAREN"
| SEMI -> "SEMI"
| SEMISEMI -> "SEMISEMI"
| HASH -> "HASH"
| HASHOP _ -> "HASHOP"
| SIG -> "SIG"
| STAR -> "STAR"
| STRING _ -> "STRING"
| STRUCT -> "STRUCT"
| THEN -> "THEN"
| TILDE -> "TILDE"
| TO -> "TO"
| TRUE -> "TRUE"
| TRY -> "TRY"
| TYPE -> "TYPE"
| UIDENT _ -> "UIDENT"
| UNDERSCORE -> "UNDERSCORE"
| VAL -> "VAL"
| VIRTUAL -> "VIRTUAL"
| WHEN -> "WHEN"
| WHILE -> "WHILE"
| WITH -> "WITH"
| COMMENT _ -> "COMMENT"
(* | PURE -> "PURE" *)
| DOCSTRING _ -> "DOCSTRING"
| EOL -> "EOL"
| QUOTED_STRING_EXPR _ -> "QUOTED_STRING_EXPR"
| QUOTED_STRING_ITEM _ -> "QUOTED_STRING_ITEM"
| METAOCAML_ESCAPE  -> "METAOCAML_ESCAPE"
| METAOCAML_BRACKET_OPEN -> "METAOCAML_BRACKET_OPEN"
| METAOCAML_BRACKET_CLOSE -> "METAOCAML_BRACKET_CLOSE"
(* | IMPLICATION -> "IMPLICATION" *)
*)

let string_of_args pp args =
  match args with
  | [] -> "()"
  | _ ->
    let a = String.concat ", " (List.map pp args) in
    Format.asprintf "(%s)" a

let rec separate li f sep : string =
  match li with
  | [] -> ""
  | [x] -> f x
  | x ::xs -> f x ^ sep ^ separate xs f sep
  ;;

let string_of_bin_op op : string =
  match op with
  | GT -> ">"
  | LT -> "<"
  | EQ -> "="
  | GTEQ -> ">="
  | LTEQ -> "<="

let string_of_constr_call n args =
  match n, args with
  | "[]", _ -> "[]"
  | "::", [a1; a2] -> Format.asprintf "%s :: %s" a1 a2
  | _ -> Format.asprintf "%s(%s)" n (String.concat ", " args)

let string_of_bin_term_op op : string =
  match op with
  | Plus -> "+"
  | Minus -> "-"
  | SConcat -> "++"
  | TAnd -> "&&"
  | TPower -> "^"
  | TTimes -> "*"
  | TDiv -> "/"
  | TOr -> "||"
  | TCons ->  "::"

let string_of_constant c : string =
  match c with
  | ValUnit -> "()"
  | Num i -> if i >= 0 then string_of_int i else "(" ^ string_of_int i ^ ")"
  | TStr s -> s
  | Nil -> "[]"
  | TTrue -> "true"
  | TFalse -> "false"

let rec string_of_term t : string =
  match t with
  | Const c -> string_of_constant c
  | BinOp (op, lhs, rhs) -> Format.asprintf "(%s %s %s)" (string_of_term lhs) (string_of_bin_term_op op) (string_of_term rhs)
  | TNot a -> Format.asprintf "not(%s)" (string_of_term a)
  | Var str -> str
  | Rel (bop, t1, t2) ->
    "(" ^ string_of_term t1 ^ (match bop with | EQ -> "==" | _ -> string_of_bin_op bop) ^ string_of_term t2 ^ ")"
  | TApp (op, args) -> Format.asprintf "%s%s" op (string_of_args string_of_term args)
  | TLambda (_name, params, sp, body) ->
    let body =
      match body with
      | None -> ""
      | Some b -> Format.asprintf "-> %s" (string_of_core_lang b)
    in
    Format.asprintf "(fun %s (*@@ %s @@*) %s)" (String.concat " " params) (Option.map string_of_staged_spec sp |> Option.value ~default:"") body
  | TTuple nLi ->
    let rec helper li =
      match li with
      | [] -> ""
      | [x] -> string_of_term x
      | x:: xs -> string_of_term x ^","^ helper xs
    in "(" ^ helper nLi ^ ")"

  | TList nLi ->
    let rec helper li =
      match li with
      | [] -> ""
      | [x] -> string_of_term x
      | x:: xs -> string_of_term x ^";"^ helper xs
    in "[" ^ helper nLi ^ "]"

and string_of_staged_spec (st:staged_spec) : string =
  match st with
  | Shift (nz, k, spec) ->
    let zero = if nz then "" else "0" in
    Format.asprintf "shift%s(%s. %s)" zero k (string_of_staged_spec spec)
  | Reset spec ->
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
    Format.asprintf "ex %s. (%s)" vs (string_of_staged_spec spec)
  (* | IndPred {name; args} -> *)
    (* Format.asprintf "%s(%s)" name (String.concat " " (List.map string_of_term args)) *)
  | TryCatch (pi, h, ( src, ((normP, normSpec), ops)), ret) ->
    let string_of_normal_case = normP ^ ": " ^ string_of_staged_spec (normSpec) in
    let string_of_eff_case (eName, param, eSpec)=  eName  ^
      (match param with | None -> " " | Some p -> "("^ p ^ ") ")^ ": " ^ string_of_staged_spec eSpec   in
    let string_of_eff_cases ops =  List.fold_left (fun acc a -> acc ^ ";\n" ^string_of_eff_case a) "" ops in
    Format.asprintf "ens %s; \n(TRY \n(%s)\nCATCH \n{%s%s}[%s])\n" (string_of_state (pi, h)) (string_of_staged_spec src) (string_of_normal_case) (string_of_eff_cases ops) (string_of_term ret)
  | Sequence (s1, s2) -> Format.sprintf "%s; %s" (string_of_staged_spec s1) (string_of_staged_spec s2)
  | Bind (v, expr, body) -> Format.sprintf "bind %s=%s. (%s)" v (string_of_staged_spec expr) (string_of_staged_spec body)
  | Disjunction (lhs, rhs) -> Format.sprintf "(%s) \\/ (%s)" (string_of_staged_spec lhs) (string_of_staged_spec rhs)

and string_of_instant (str, ar_Li): string =
  (* syntax is like OCaml type constructors, e.g. Foo, Foo (), Foo (1, ()) *)
  let args =
    match ar_Li with
    | [] -> ""
    | [t] -> Format.sprintf "(%s)" (string_of_term t)
    | _ -> Format.sprintf "(%s)" (separate (ar_Li) (string_of_term) (","));
  in
  Format.sprintf "%s%s" str args


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


and  string_of_effect_cases_specs (h_ops:(string * string option * staged_spec) list): string =
  match h_ops with
  | [] -> ""
  | [(effname, param, spec)] ->
    (effname  ^  (match param with | None -> " " | Some p -> "("^ p ^ ") ")^ ": " ^
    string_of_staged_spec spec)
  | (effname, param, spec) ::xs ->
    (effname  ^  (match param with | None -> " " | Some p -> "("^ p ^ ") ")^ ": " ^
    string_of_staged_spec spec ^ "\n"
    ) ^ string_of_effect_cases_specs xs


and string_of_normal_case_specs ((param, h_norm):(string * staged_spec)): string =
  ((match param with | p -> p ^ "")^ ": " ^ string_of_staged_spec (h_norm));

and string_of_handlingcases ((h_normal, h_ops):handlingcases) : string =
    "{\n" ^
    string_of_normal_case_specs h_normal ^ "\n" ^
    string_of_effect_cases_specs h_ops
    ^ "\n}\n"



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

and string_of_lemma l =
  Format.asprintf "%s: forall %s, %s <: %s" l.l_name (string_of_list Fun.id l.l_params) (string_of_instant l.l_left) (string_of_staged_spec l.l_right)

and string_of_core_lang (e:core_lang) :string =
  match e with
  | CValue v -> string_of_term v
  | CLet (v, e, e1) -> Format.sprintf "let %s = %s in\n%s" v (string_of_core_lang e) (string_of_core_lang e1)
  | CIfELse (pi, t, e) -> Format.sprintf "if %s then %s else (%s)" (string_of_pi pi)  (string_of_core_lang t) (string_of_core_lang e)
  | CFunCall (f, [a; b]) when not (is_alpha (String.get f 0)) -> Format.sprintf "%s %s %s" (string_of_term a) f (string_of_term b)
  | CFunCall (f, xs) -> Format.sprintf "%s %s" f (List.map string_of_term xs |> String.concat " ")
  | CWrite (v, e) -> Format.sprintf "%s := %s" v (string_of_term e)
  | CRef v -> Format.sprintf "ref %s" (string_of_term v)
  | CRead v -> Format.sprintf "!%s" v
  | CAssert (p, h) -> Format.sprintf "assert (%s && %s)" (string_of_pi p) (string_of_kappa h)
  | CPerform (eff, Some arg) -> Format.sprintf "perform %s %s" eff (string_of_term arg)
  | CPerform (eff, None) -> Format.sprintf "perform %s" eff
  | CMatch (typ, None, e, vs, hs, cs) -> Format.sprintf "match[%s] %s with\n%s%s%s" (string_of_handler_type typ) (string_of_core_lang e) (match vs with | Some (v, norm) -> Format.asprintf "| %s -> %s\n" v (string_of_core_lang norm) | _ -> "") (match hs with | [] -> "" | _ :: _ -> string_of_core_handler_ops hs ^ "\n") (match cs with [] -> "" | _ :: _ -> string_of_constr_cases cs)
  | CMatch (typ, Some spec, e, vs, hs, cs) -> Format.sprintf "match[%s] %s%s with\n%s%s\n%s" (string_of_handler_type typ) (string_of_try_catch_lemma spec) (string_of_core_lang e) (match vs with | Some (v, norm) -> Format.asprintf "| %s -> %s\n" v (string_of_core_lang norm) | _ -> "") (string_of_core_handler_ops hs) (string_of_constr_cases cs)
  | CResume tList -> Format.sprintf "continue %s" (List.map string_of_term tList |> String.concat " ")
  | CLambda (xs, spec, e) -> Format.sprintf "fun %s%s -> %s" (String.concat " " xs) (match spec with None -> "" | Some ds -> Format.asprintf " (*@@ %s @@*)" (string_of_staged_spec ds)) (string_of_core_lang e)
  | CShift (b, k, e) -> Format.sprintf "Shift%s %s -> %s" (if b then "" else "0") k (string_of_core_lang e)
  | CReset (e) -> Format.sprintf "<%s>" (string_of_core_lang e)

and string_of_intermediate (i : intermediate) =
  match i with
  | Eff name -> Format.sprintf "effect %s" name
  | Lem lemma -> Format.sprintf "lemma %s" (string_of_lemma lemma)
  | LogicTypeDecl _ -> Format.sprintf "[pure type]"
  | Meth (name, params, spec, body, _tactics, _fn_info) ->
      Format.sprintf "let %s %s (*@@ %s @@*) = %s"
      name
      (String.concat ", " params)
      (Option.fold ~none:"" ~some:string_of_staged_spec spec)
      (string_of_core_lang body)
  | Pred _ -> "[predicate]"
  | SLPred _ -> "[sl predicate]"

and string_of_constr_cases cs =
  cs |> List.map (fun (n, args, body) -> Format.asprintf "| %s -> %s" (string_of_constr_call n args) (string_of_core_lang body)) |> String.concat "\n"

and string_of_core_handler_ops hs =
  List.map (fun (name, v, spec, body) ->
    let spec = spec |> Option.map (fun s -> Format.asprintf " (*@@ %s @@*)" (string_of_staged_spec s)) |> Option.value ~default:"" in
    Format.asprintf "| effect %s k%s -> %s"
      (match v with None -> name | Some v -> Format.asprintf "(%s %s)" name v) spec (string_of_core_lang body)) hs |> String.concat "\n"

(*

let find_rec p_name =
  object(self)
    inherit [_] reduce_spec as super
    method zero = false
    method plus = (||)

    method! visit_HigherOrder _ ((_p, _h, (f, _a), _r) as fn) =
      self#plus (f = p_name) (super#visit_HigherOrder () fn)

    method! visit_Atomic () op a b =
      match op with
      | EQ -> (match (a, b) with
        | (Var x, Var y) -> x = p_name || y = p_name
        | _ -> false)
      | _ -> false
  end
(**********************************************)
exception FooAskz3 of string



let rec getAllVarFromTerm (t:term) (acc:string list):string list =
  match t with
| Var ( name) -> List.append acc [name]
| Plus (t1, t2) ->
    let cur = getAllVarFromTerm t1 acc in
    getAllVarFromTerm t2 cur
| Minus (t1, t2) ->
    let cur = getAllVarFromTerm t1 acc in
    getAllVarFromTerm t2 cur
| _ -> acc
;;

let string_of_pred ({ p_name; p_params; p_body; _ } : pred_def) : string =
  Format.asprintf "%s(%s) == %s" p_name (String.concat "," p_params) (string_of_spec_list p_body)

let string_of_inclusion (lhs:spec list) (rhs:spec list) :string =
  string_of_spec_list lhs ^" |- " ^string_of_spec_list rhs

let string_of_effect_stage1 (vs, pre, post, eff, ret) =
  Format.asprintf "ex %s. req %s; ens %s /\\ %s /\\ res=%s" (String.concat " " vs) (string_of_state pre) (string_of_state post) (string_of_instant eff) (string_of_term ret)

let string_of_effect_stage {e_evars = vs; e_pre = pre; e_post = post; e_constr = eff; e_ret = ret; _} =
  Format.asprintf "ex %s. req %s; ens %s /\\ %s /\\ res=%s" (String.concat " " vs) (string_of_state pre) (string_of_state post) (string_of_instant eff) (string_of_term ret)

let string_of_normal_stage (vs, pre, post, ret) =
  Format.asprintf "ex %s. req %s; ens %s /\\ res=%s" (String.concat " " vs) (string_of_state pre) (string_of_state post) (string_of_term ret)
*)
let string_of_existentials vs =
  match vs with
  | [] -> ""
  | _ :: _ -> Format.asprintf "ex %s. " (String.concat "," vs)

let string_of_result b = if b then green "true" else red "false"

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

(* let string_of_time = string_of_float *)
let string_of_time = Format.asprintf "%.0f"

let string_of_sset s =
  Format.asprintf "{%s}" (String.concat ", " (SSet.elements s))

let string_of_smap pp s =
  Format.asprintf "{%s}" (String.concat ", " (List.map (fun (k, v) -> Format.asprintf "%s -> %s" k (pp v)) (SMap.bindings s)))

let rec string_of_type t =
  match t with
  | TyString -> "string"
  | Int -> "int"
  | Unit -> "unit"
  | TConstr (name, args) -> Format.asprintf "(%s) %s" (List.map string_of_type args |> String.concat ",") name
  | List_int -> "intlist"
  | Bool -> "bool"
  | Lamb -> "lambda"
  | TVar v -> Format.asprintf "'%s" v
  | Arrow (t1, t2) -> Format.asprintf "%s->%s" (string_of_type t1) (string_of_type t2)

let string_of_pure_fn ({ pf_name; pf_params; pf_ret_type; pf_body } : pure_fn_def) : string =
  Format.asprintf "let %s %s : %s = %s" pf_name (String.concat " " (List.map (fun (p, t) -> Format.asprintf "(%s:%s)" p (string_of_type t)) pf_params)) (string_of_type pf_ret_type) (string_of_core_lang pf_body)

(* let string_of_tmap pp s = *)
(*   Format.asprintf "{%s}" (String.concat ", " (List.map (fun (k, v) -> Format.asprintf "%s -> %s" (string_of_type k) (pp v)) (TMap.bindings s))) *)
(**)
(* let string_of_abs_env t = *)
(*   Format.asprintf "%s, %s" (string_of_smap string_of_type t.vartypes)  *)
(*   (* "<opaque>" *) *)
(* (string_of_tmap string_of_type (TMap.map (fun t -> U.get t) !(t.equalities))) *)

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
    (match m.m_params with | [] -> "()" | _ -> String.concat " " m.m_params)
    ((match m.m_spec with None -> "" | Some s -> Format.asprintf "(*@@ %s @@*)\n" (string_of_staged_spec s)))
    (string_of_core_lang m.m_body)

let string_of_program (cp:core_program) :string =
  List.map string_of_meth_def cp.cp_methods |> String.concat "\n\n"

(* let string_of_lambda_obl (o:lambda_obligation) :string = *)
(*   Format.asprintf "%s:\n%s\n|-\n%s\n<:\n%s" *)
(*   o.lo_name (string_of_smap string_of_pred o.lo_preds) (string_of_staged_spec o.lo_left) (string_of_staged_spec o.lo_right) *)
(**)
(* let string_of_obl (d:(staged_spec * staged_spec)) :string = *)
(*   (string_of_pair string_of_staged_spec string_of_staged_spec) d *)
(**)
(* let string_of_pobl (d:(string list * (staged_spec * staged_spec))) :string = *)
(*   string_of_pair (string_of_args Fun.id) string_of_obl d *)

(*
(* implements the [pi = pi_other and pi_res] split from the ho paper *)
let rec split_res p =
  match p with
  | True -> True, []
  | False -> False, []
  | Atomic (_, Var "res", _)
  | Atomic (_, _, Var "res") -> True, [p]
  | Atomic (_, _, _) -> p, []
  | And (a, b) ->
    let l, r = split_res a in
    let l1, r1 = split_res b in
    And (l, l1), r @ r1
  | Or (a, b) ->
    let l, r = split_res a in
    let l1, r1 = split_res b in
    Or (l, l1), r @ r1
  | Imply (a, b) ->
    let l, r = split_res a in
    let l1, r1 = split_res b in
    Imply (l, l1), r @ r1
  | Not a ->
    let l, r = split_res a in
    Not l, r
  | Predicate (_, _) -> p, []
  | Subsumption (_, _) -> p, []

let split_res_fml p =
  let rest, constrs = split_res p in
  let fml = List.fold_right (fun c t -> And (c, t)) constrs True in
  rest, fml

let get_res_value p =
  let _rest, eqs = split_res p in
  match eqs with
  | [Atomic (EQ, Var "res", t)]
  | [Atomic (EQ, t, Var "res")] -> Some t
  | [Atomic (_, _, _)] ->
    (* failwith (Format.asprintf "not an equality on res: %s" (string_of_pi p)) *)
    None
  | [] ->
    (* failwith (Format.asprintf "no mention of res: %s" (string_of_pi p)) *)
    None
  | _ ->
    (* failwith (Format.asprintf "many possible res values: %s" (string_of_pi p)) *)
    None

let get_res_value_exn p =
  get_res_value p |> Option.get

let is_just_res_of pi t =
  match get_res_value pi with
  | None -> false
  | Some r -> r = t

let lambda_to_pred_def name t =
  match t with
  | TLambda (_lid, params, spec, _body) ->
    {
      p_name = name;
      p_params = params;
      p_body = spec;
      p_rec = (find_rec name)#visit_disj_spec () spec;
    }
  | _ ->
    failwith
      (Format.asprintf "cannot convert term to predicate: %s" (string_of_term t))

let local_lambda_defs =
  object
    inherit [_] reduce_spec
    method zero = SMap.empty
    method plus = SMap.merge_disjoint

    method! visit_TLambda _ _ _ _ _ = SMap.empty

    method! visit_Subsumption () a b =
      match a, b with
      | Var v, TLambda _ ->
        SMap.singleton v (lambda_to_pred_def v b)
      | _ -> SMap.empty

    method! visit_Atomic () op a b =
      match op, a, b with
      | (EQ, (TLambda _ as l), Var v) | (EQ, Var v, (TLambda _ as l)) ->
        SMap.singleton v (lambda_to_pred_def v l)
      | _ -> SMap.empty
  end
 *)
