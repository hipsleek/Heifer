(* * Functions for printing the typed AST.

open Common
open Typedhip

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

let verifier_counter: int ref = ref 0;;

(* only for testing! to make tests deterministic *)
let verifier_counter_reset () = verifier_counter := 0
let verifier_counter_reset_to n = verifier_counter := n

let end_of_var = Str.regexp "_?[0-9]+$"
let verifier_getAfreeVar ?(typ= new_type_var ()) _from : binder  =
  (* this prefix shows provenance, but that turned out to be useless *)
  (* let prefix = from |> Option.map (fun v -> v ^ "_") |> Option.value ~default:"_f" in *)
  let prefix =
    (* match from with *)
    (* | None -> "_f" *)
    (* | Some f -> *)
      (* Str.global_replace end_of_var "" from *)
      "v"
  in
  let x = prefix ^ string_of_int (!verifier_counter) in
  incr verifier_counter;
  (x, typ)

(* let%expect_test _ =
  let p = print_endline in
  verifier_counter_reset ();
  p (verifier_getAfreeVar "v");
  p (verifier_getAfreeVar "v");
  p (verifier_getAfreeVar "a");
  let v = verifier_getAfreeVar "a" in
  p v;
  p (verifier_getAfreeVar v);
  [%expect
  {|
    v0
    v1
    v2
    v3
    v4
  |}] *)

let string_of_type = Pretty.string_of_type

let string_of_binder ((ident, typ) : binder) =
  Format.sprintf "(%s : %s)" ident (string_of_type typ)

let string_of_args pp args =
  match args with
  | [] -> "()"
  | _ ->
    let a = String.concat ", " (List.map pp args) in
    Format.asprintf "(%s)" a

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

  ;;

let rec separate li f sep : string =
  match li with
  | [] -> ""
  | [x] -> f x
  | x ::xs -> f x ^ sep ^ separate xs f sep




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
  | "::", [a1; a2] -> Format.asprintf "%s :: %s" (string_of_binder a1) (string_of_binder a2)
  | _ -> Format.asprintf "%s(%s)" n (String.concat ", " (List.map string_of_binder args))

let rec string_of_term t : string =
  Pretty.string_of_term (Untypehip.untype_term t)

and string_of_staged_spec (st:stagedSpec) : string =
  Pretty.string_of_staged_spec (Untypehip.untype_staged_spec st)

and string_of_spec (spec:spec) :string =
  match spec with
  | [] -> "<empty spec>"
  | _ ->
    spec
    (* |> List.filter (function Exists [] -> false | _ -> true) *)
    |> List.map string_of_staged_spec |> String.concat "; "

and string_of_spec_list (specs:spec list) : string =
  match specs with
  | [] -> "<empty disj>"
  | _ :: _ -> List.map string_of_spec specs |> String.concat " \\/ "

and string_of_disj_spec (s:disj_spec) : string = string_of_spec_list s

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


and  string_of_effect_cases_specs (h_ops:(string * string option * disj_spec) list): string = 
  match h_ops with 
  | [] -> ""
  | [(effname, param, spec)] -> 
    (effname  ^  (match param with | None -> " " | Some p -> "("^ p ^ ") ")^ ": " ^ 
    string_of_disj_spec spec)
  | (effname, param, spec) ::xs -> 
    (effname  ^  (match param with | None -> " " | Some p -> "("^ p ^ ") ")^ ": " ^ 
    string_of_disj_spec spec ^ "\n"
    ) ^ string_of_effect_cases_specs xs 


and string_of_normal_case_specs ((param, h_norm):(string * disj_spec)): string = 
  ((match param with | p -> p ^ "")^ ": " ^ string_of_disj_spec (h_norm)); 

and string_of_handlingcases ((h_normal, h_ops):handlingcases) : string = 
    "{\n" ^ 
    string_of_normal_case_specs h_normal ^ "\n" ^ 
    string_of_effect_cases_specs h_ops 
    ^ "\n}\n"



and string_of_try_catch_lemma (x:tryCatchLemma) : string = 
  let (tcl_head, tcl_handledCont, (*(h_normal, h_ops),*) tcl_summary) = x in 
  "TRY " 
  ^ 
  string_of_spec tcl_head 

  ^ (match tcl_handledCont with 
  | None -> "" | Some conti -> " # " ^ string_of_disj_spec conti)

  
  ^ " CATCH \n" (*^ string_of_handlingcases (h_normal, h_ops ) *)
  ^ "=> " ^ string_of_disj_spec tcl_summary

and string_of_handler_type (h:handler_type) : string = 
    match h with
    | Deep -> "d"
    | Shallow -> "s"

and string_of_core_lang (e:core_lang) :string =
  match e.core_desc with
  | CValue v -> string_of_term v
  | CLet (v, e, e1) -> Format.sprintf "let %s = %s in\n%s" v (string_of_core_lang e) (string_of_core_lang e1)
  | CIfElse (pi, t, e) -> Format.sprintf "if %s then %s else (%s)" (string_of_pi pi)  (string_of_core_lang t) (string_of_core_lang e)
  | CFunCall (f, [a; b]) when not (is_alpha (String.get f 0)) -> Format.sprintf "%s %s %s" (string_of_term a) f (string_of_term b)
  | CFunCall (f, xs) -> Format.sprintf "%s %s" f (List.map string_of_term xs |> String.concat " ")
  | CWrite (v, e) -> Format.sprintf "%s := %s" v (string_of_term e)
  | CRef v -> Format.sprintf "ref %s" (string_of_term v)
  | CRead v -> Format.sprintf "!%s" v
  | CAssert (p, h) -> Format.sprintf "assert (%s && %s)" (string_of_pi p) (string_of_kappa h)
  | CPerform (eff, Some arg) -> Format.sprintf "perform %s %s" eff (string_of_term arg)
  | CPerform (eff, None) -> Format.sprintf "perform %s" eff
  | CMatch (typ, None, e, vs, hs, cs) -> Format.sprintf "match[%s] %s with\n%s%s%s" (string_of_handler_type typ) (string_of_core_lang e) (match vs with | Some (v, norm) -> Format.asprintf "| %s -> %s\n" (string_of_binder v) (string_of_core_lang norm) | _ -> "") (match hs with | [] -> "" | _ :: _ -> string_of_core_handler_ops hs ^ "\n") (match cs with [] -> "" | _ :: _ -> string_of_constr_cases cs)
  | CMatch (typ, Some spec, e, vs, hs, cs) -> Format.sprintf "match[%s] %s%s with\n%s%s\n%s" (string_of_handler_type typ) (string_of_try_catch_lemma spec) (string_of_core_lang e) (match vs with | Some (v, norm) -> Format.asprintf "| %s -> %s\n" (string_of_binder v) (string_of_core_lang norm) | _ -> "") (string_of_core_handler_ops hs) (string_of_constr_cases cs)
  | CResume tList -> Format.sprintf "continue %s" (List.map string_of_term tList |> String.concat " ")
  | CLambda (xs, spec, e) -> Format.sprintf "fun %s%s -> %s" (String.concat " " (List.map string_of_binder xs)) (match spec with None -> "" | Some ds -> Format.asprintf " (*@@ %s @@*)" (string_of_disj_spec ds)) (string_of_core_lang e)
  | CShift (b, k, e) -> Format.sprintf "Shift%s %s -> %s" (if b then "" else "0") (string_of_binder k) (string_of_core_lang e)

  | CReset (e) -> Format.sprintf "<%s>" (string_of_core_lang e)


and string_of_constr_cases cs =
  cs |> List.map (fun (n, args, body) -> Format.asprintf "| %s -> %s" (string_of_constr_call n args) (string_of_core_lang body)) |> String.concat "\n"

and string_of_core_handler_ops hs =
  List.map (fun (name, v, spec, body) ->
    let spec = spec |> Option.map (fun s -> Format.asprintf " (*@@ %s @@*)" (string_of_disj_spec s)) |> Option.value ~default:"" in
    Format.asprintf "| effect %s k%s -> %s"
      (match v with None -> name | Some v -> Format.asprintf "(%s %s)" name v) spec (string_of_core_lang body)) hs |> String.concat "\n"

let rec stricTcompareTerm (term1:term) (term2:term) : bool =
  let same_term = match (term1.term_desc, term2.term_desc) with
    (Var s1, Var s2) -> String.compare s1 s2 == 0
  | (Const Num n1, Const Num n2) -> n1 == n2
  | (BinOp (op1, lhs1, rhs1), BinOp(op2, lhs2, rhs2)) -> op1 == op2 && stricTcompareTerm lhs1 rhs1 && stricTcompareTerm lhs2 rhs2
  | (Const ValUnit, Const ValUnit) -> true
  | _ -> false
  in
  let same_type = term1.term_type = term2.term_type in
  same_term && same_type


let rec comparePure (pi1:pi) (pi2:pi):bool =
  match (pi1 , pi2) with
    (True, True) -> true
  | (False, False) -> true
  | (Atomic(GT, t1, t11),  Atomic(GT, t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Atomic (LT, t1, t11),  Atomic(LT, t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Atomic (GTEQ, t1, t11),  Atomic(GTEQ, t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Atomic (LTEQ, t1, t11),  Atomic(LTEQ, t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Atomic (EQ, t1, t11),  Atomic(EQ, t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Or (p1, p2), Or (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (And (p1, p2), And (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (Not p1, Not p2) -> comparePure p1 p2
  | _ -> false
  ;;

let rec getAllPi piIn acc=
    (match piIn with
      And (pi1, pi2) -> (getAllPi pi1 acc ) @ (getAllPi pi2 acc )
    | _ -> acc  @[piIn]
    )
    ;;

let rec existPi pi li =
    (match li with
      [] -> false
    | x :: xs -> if comparePure pi x then true else existPi pi xs
    )
    ;;

let find_rec p_name =
  object(self)
    inherit [_] reduce_spec as super
    method zero = false
    method plus = (||)

    method! visit_HigherOrder _ ((_p, _h, (f, _a), _r) as fn) =
      self#plus (f = p_name) (super#visit_HigherOrder () fn)

    method! visit_Atomic () op a b =
      match op with
      | EQ -> (match (a.term_desc, b.term_desc) with
        | (Var x, Var y) -> x = p_name || y = p_name
        | _ -> false)
      | _ -> false
  end

(**********************************************)
exception FooAskz3 of string



let rec getAllVarFromTerm (t:term) (acc:binder list):binder list =
  match t.term_desc with
  | Var ( name) -> List.append acc [(name, t.term_type)]
  | BinOp(_, lhs, rhs) ->
      let cur = getAllVarFromTerm lhs acc in
      getAllVarFromTerm rhs cur
  | _ -> acc
  ;;

let addAssert (str:string) :string =
  "(assert " ^ str ^ " ) \n (check-sat) \n"
  ;;

let rec kappaToPure kappa : pi =
  match kappa with
  | EmptyHeap -> True
  | PointsTo (str, t) -> Atomic(EQ, {term_desc = Var str; term_type = t.term_type}, t)
  | SepConj (k1, k2) -> And (kappaToPure k1, kappaToPure k2)

  (* | Implication (k1, k2) -> Imply (kappaToPure k1, kappaToPure k2) *)

let string_of_pred ({ p_name; p_params; p_body; _ } : pred_def) : string =
  Format.asprintf "%s(%s) == %s" p_name (String.concat "," (List.map string_of_binder p_params)) (string_of_spec_list p_body)

let string_of_inclusion (lhs:spec list) (rhs:spec list) :string =
  string_of_spec_list lhs ^" |- " ^string_of_spec_list rhs

let string_of_effHOTryCatchStages s =
  match s with
  | (EffHOStage x) ->
    (let {e_pre = (p1, h1); e_post = (p2, h2); _} = x in
    let ex = match x.e_evars with [] -> [] | _ -> [Exists x.e_evars] in
    let current = ex @ [Require(p1, h1);
    (match x.e_typ with
    | `Eff -> RaisingEff(p2, h2, x.e_constr, x.e_ret)
    | `Fn -> HigherOrder(p2, h2, x.e_constr, x.e_ret))] in
    string_of_spec current )

  | ShiftStage x ->
    let ex = match x.s_evars with [] -> [] | _ -> [Exists x.s_evars] in
    let current = ex @ [Shift (x.s_notzero, x.s_cont, x.s_body, x.s_ret)] in
    string_of_spec current

  | (TryCatchStage ct) -> 
    (let {tc_pre = (p1, h1); tc_post = (p2, h2); _} = ct in
    let ex = match ct.tc_evars with [] -> [] | _ -> [Exists ct.tc_evars] in
    let current = ex @ 
    [Require(p1, h1);
    (TryCatch(p2, h2, ct.tc_constr ,ct.tc_ret)
    )
    ] in
    string_of_spec current )
  
  | (ResetStage ct) -> 
    (let {rs_pre = (p1, h1); rs_post = (p2, h2); _} = ct in
    let ex = match ct.rs_evars with [] -> [] | _ -> [Exists ct.rs_evars] in
    let current = ex @ 
    [Require(p1, h1); NormalReturn (p2, h2);
    (Reset(ct.rs_body, ct.rs_ret)
    )
    ] in
    string_of_spec current )

let rec string_of_normalisedStagedSpec (spec:normalisedStagedSpec) : string =
  let (effS, normalS) = spec in
  match effS with
  | [] ->
    let (existiental, (p1, h1), (p2, h2)) = normalS in
    let ex = match existiental with [] -> [] | _ -> [Exists existiental] in
    let current = ex @ [Require(p1, h1); NormalReturn(p2, h2)] in
    string_of_spec current
  | x :: xs  ->
    string_of_effHOTryCatchStages x
    ^ "; " ^ string_of_normalisedStagedSpec (xs, normalS)

let string_of_normalisedStagedSpecList (specs:normalisedStagedSpec list) : string =
  match specs with
  | [] -> "<empty disj>"
  | _ :: _ -> List.map string_of_normalisedStagedSpec specs |> String.concat " \\/ "
let string_of_effect_stage1 (vs, pre, post, eff, ret) =
  Format.asprintf "ex %s. req %s; ens %s /\\ %s /\\ res=%s" (String.concat " " vs) (string_of_state pre) (string_of_state post) (string_of_instant eff) (string_of_term ret)

let string_of_effect_stage {e_evars = vs; e_pre = pre; e_post = post; e_constr = eff; e_ret = ret; _} =
  Format.asprintf "ex %s. req %s; ens %s /\\ %s /\\ res=%s" (String.concat " " (List.map string_of_binder vs)) (string_of_state pre) (string_of_state post) (string_of_instant eff) (string_of_term ret)

let string_of_normal_stage (vs, pre, post, ret) =
  Format.asprintf "ex %s. req %s; ens %s /\\ res=%s" (String.concat " " (List.map string_of_binder vs)) (string_of_state pre) (string_of_state post) (string_of_term ret)

let string_of_existentials vs =
  match vs with
  | [] -> ""
  | _ :: _ -> Format.asprintf "ex %s. " (String.concat "," (List.map string_of_binder vs))

let string_of_res b = if b then green "true" else red "false"

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

let string_of_lemma l =
  Format.asprintf "%s: forall %s, %s <: %s" l.l_name (string_of_list string_of_binder l.l_params) (string_of_instant l.l_left) (string_of_spec l.l_right)

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
    ((match m.m_spec with None -> "" | Some s -> s |> List.map string_of_spec |> List.map (Format.asprintf "(*@@ %s @@*)") |> String.concat "\n\\/\n" |> fun s -> s ^ "\n"))
    (string_of_core_lang m.m_body)

let string_of_program (cp:core_program) :string =
  List.map string_of_meth_def cp.cp_methods |> String.concat "\n\n"

let string_of_lambda_obl (o:lambda_obligation) :string =
  Format.asprintf "%s:\n%s\n|-\n%s\n<:\n%s"
  o.lo_name (string_of_smap string_of_pred o.lo_preds) (string_of_disj_spec o.lo_left) (string_of_disj_spec o.lo_right)

let string_of_obl (d:(disj_spec * disj_spec)) :string =
  (string_of_pair string_of_disj_spec string_of_disj_spec) d

let string_of_pobl (d:(binder list * (disj_spec * disj_spec))) :string =
  string_of_pair (string_of_args string_of_binder) string_of_obl d

(* implements the [pi = pi_other and pi_res] split from the ho paper *)
let rec split_res p =
  match p with
  | True -> True, []
  | False -> False, []
  | Atomic (_, {term_desc = Var "res"; _}, _)
  | Atomic (_, _, {term_desc = Var "res"; _}) -> True, [p]
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
  | [Atomic (EQ, {term_desc = Var "res"; _}, t)]
  | [Atomic (EQ, t, {term_desc = Var "res"; _})] -> Some t
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
  match t.term_desc with
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
      match a.term_desc, b.term_desc with
      | Var v, TLambda _ ->
        SMap.singleton v (lambda_to_pred_def v b)
      | _ -> SMap.empty

    method! visit_Atomic () op a b =
      match op, a, b with
      | (EQ, ({term_desc = TLambda _; _} as l), {term_desc = Var v; _}) | (EQ, {term_desc = Var v; _}, ({term_desc = TLambda _; _} as l)) ->
        SMap.singleton v (lambda_to_pred_def v l)
      | _ -> SMap.empty
  end

let bindFormalNActual (formal: binder list) (actual: core_value list) : ((binder * core_value) list)= 
  try List.map2 pair formal actual
  with 
  | Invalid_argument _ -> 
    print_endline ("formal: " ^ (List.map string_of_binder formal |> String.concat ", "));
    print_endline ("actual: " ^ (List.map (fun a-> string_of_term a) actual |> String.concat ", "));
    print_endline ("bindFormalNActual length not equal");
    []
  

  (*
  match (formal, actual) with 
  | (x::xs, y::ys) -> (x, y)::bindFormalNActual xs ys 
  | ([], []) -> [] 
  | _ -> []   
  *)

let bindNewNames (formal: string list) (actual: string list) : ((string * string) list)= 
  try List.map2 pair formal actual
  with 
  | Invalid_argument _ -> 
    print_endline ("formal: " ^ (List.map (fun a-> a) formal |> String.concat ", "));
    print_endline ("actual: " ^ (List.map (fun a-> a) actual |> String.concat ", "));
    failwith ("bindNewNames length not equle")
  
let function_stage_to_disj_spec constr args ret =
  (* TODO for some reason this version isn't handled by normalization *)
  (* [[HigherOrder (True, EmptyHeap, l.l_left, res_v)]] *)
  let v = verifier_getAfreeVar "v" in
  let v_var = let (name, typ) = v in {term_desc = Var name; term_type = typ} in
  [[Exists [v]; HigherOrder (True, EmptyHeap, (constr, args), v_var); NormalReturn (Atomic (EQ, ret, v_var), EmptyHeap)]]


let startingFromALowerCase (label:string) : bool = 
  let c = label.[0] in 
  if Char.code c >= 97 then true else false 


let retriveFormalArg arg :string = 
  match arg.term_desc  with 
  | Var ret -> ret
  | _ -> 
        print_endline (string_of_term arg);
        failwith "effect return is not var 1" *)
