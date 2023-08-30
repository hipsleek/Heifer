(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open Printf
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
let emph text = col ~ansi:"\u{001b}[1;4m" ~html:"<span class=\"output-emph\">" text

let verifier_counter: int ref = ref 0;;

(* only for testing! to make tests deterministic *)
let verifier_counter_reset () = verifier_counter := 0
let verifier_counter_reset_to n = verifier_counter := n

let end_of_var = Str.regexp "_?[0-9]+$"
let verifier_getAfreeVar from :string  =
  (* this prefix shows provenance, but that turned out to be useless *)
  (* let prefix = from |> Option.map (fun v -> v ^ "_") |> Option.value ~default:"_f" in *)
  let prefix =
    (* match from with *)
    (* | None -> "_f" *)
    (* | Some f -> *)
      Str.global_replace end_of_var "" from
  in
  let x = prefix ^ string_of_int (!verifier_counter) in 
  incr verifier_counter;
  x 

let%expect_test _ =
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
    a2
    a3
    a4
  |}]


let string_of_args pp args =
  match args with
  | [] -> "()"
  | _ ->
    let a = String.concat ", " (List.map pp args) in
    Format.asprintf "(%s)" a

let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, _) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;

let rule ?(children=[]) ?(success=true) ~name fmt = Format.kasprintf (fun s -> Node (Format.asprintf "[%s]%s %s" name (if success then "" else red " FAIL") s, children)) fmt

type proof = binary_tree

let string_of_proof tree = printTree
~line_prefix:"│"
(* ~line_prefix:" " *)
~get_name ~get_children tree

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
  ;;




let string_of_bin_op op : string =
  match op with 
  | GT -> ">" 
  | LT -> "<" 
  | EQ -> "=" 
  | GTEQ -> ">="
  | LTEQ -> "<="

let rec string_of_term t : string = 
  match t with 
  | Num i -> string_of_int i 
  | UNIT -> "()"
  | Nil -> "[]"
  | TTrue -> "true"
  | TFalse -> "false"
  | TNot a -> Format.asprintf "not(%s)" (string_of_term a)
  | TAnd (a, b) -> Format.asprintf "%s && %s" (string_of_term a) (string_of_term b)
  | TOr (a, b) -> Format.asprintf "%s || %s" (string_of_term a) (string_of_term b)
  | Var str -> str
  | Rel (bop, t1, t2) ->
    string_of_term t1 ^ (match bop with | EQ -> "==" | _ -> string_of_bin_op bop) ^ string_of_term t2
  | Plus (t1, t2) -> string_of_term t1 ^ "+" ^ string_of_term t2
  | Minus (t1, t2) -> string_of_term t1 ^ "-" ^ string_of_term t2
  | TApp (op, args) -> Format.asprintf "%s%s" op (string_of_args string_of_term args)
  | TLambda name -> Format.asprintf "lambda(%s)" name
  | TTupple nLi -> 
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


let rec string_of_pi pi : string = 
  match pi with 
  | True -> "T"
  | False -> "F"
  | Atomic (op, t1, t2) -> string_of_term t1 ^ string_of_bin_op op ^ string_of_term t2
  | And   (p1, p2) -> string_of_pi p1 ^ "/\\" ^ string_of_pi p2
  | Or     (p1, p2) -> string_of_pi p1 ^ "\\/" ^ string_of_pi p2
  | Imply  (p1, p2) -> string_of_pi p1 ^ "=>" ^ string_of_pi p2
  | Not    p -> "not(" ^ string_of_pi p ^ ")"
  | Predicate (str, t) -> str ^ "(" ^ string_of_term t ^ ")"



let rec stricTcompareTerm (term1:term) (term2:term) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> String.compare s1 s2 == 0
  | (Num n1, Num n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (UNIT, UNIT) -> true 
  | _ -> false 
  ;;


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





let addAssert (str:string) :string =
  "(assert " ^ str ^ " ) \n (check-sat) \n"
  ;;










let rec kappaToPure kappa : pi =
  match kappa with 
  | EmptyHeap -> True
  | PointsTo (str, t) -> Atomic(EQ, Var str, t)
  | SepConj (k1, k2) -> And (kappaToPure k1, kappaToPure k2)

  (* | Implication (k1, k2) -> Imply (kappaToPure k1, kappaToPure k2) *)






let string_of_instant (str, ar_Li): string = 
  (* syntax is like OCaml type constructors, e.g. Foo, Foo (), Foo (1, ()) *)
  let args =
    match ar_Li with
    | [] -> ""
    | [t] -> Format.sprintf "(%s)" (string_of_term t)
    | _ -> Format.sprintf "(%s)" (separate (ar_Li) (string_of_term) (","));
  in
  Format.sprintf "%s%s" str args


let rec string_of_kappa (k:kappa) : string = 
  match k with
  | EmptyHeap -> "emp"
  | PointsTo  (str, args) -> Format.sprintf "%s->%s" str (List.map string_of_term [args] |> String.concat ", ")
  | SepConj (k1, k2) -> string_of_kappa k1 ^ "*" ^ string_of_kappa k2 
  (*| MagicWand (k1, k2) -> "(" ^ string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  ^ ")" *)
  (* | Implication (k1, k2) -> string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  *)

let string_of_state (p, h) : string =
  match h, p with
  | _, True -> string_of_kappa h
  | EmptyHeap, _ -> string_of_pi p
  | _ ->
    Format.asprintf "%s /\\ %s" (string_of_kappa h) (string_of_pi p)
    (* Format.asprintf "%s*%s" (string_of_kappa h) (string_of_pi p) *)

let string_of_staged_spec (st:stagedSpec) : string =
  match st with
  | Require (p, h) ->
    Format.asprintf "req %s" (string_of_state (p, h))
  | HigherOrder (pi, h, (f, args), ret) ->
    Format.asprintf "%s$(%s, %s, %s)" f (string_of_state (pi, h)) (string_of_args string_of_term args) (string_of_term ret)
  | NormalReturn (pi, heap, ret) ->
    Format.asprintf "Norm(%s, %s)" (string_of_state (pi, heap))  (string_of_term ret)
  | RaisingEff (pi, heap, (name, args), ret) ->
    Format.asprintf "%s(%s, %s, %s)" name (string_of_state (pi, heap)) (string_of_args string_of_term args) (string_of_term ret)
  | Exists vs ->
    Format.asprintf "ex %s" (String.concat " " vs)
  (* | IndPred {name; args} -> *)
    (* Format.asprintf "%s(%s)" name (String.concat " " (List.map string_of_term args)) *)

let string_of_spec (spec:spec) :string =
  match spec with
  | [] -> "<empty spec>"
  | _ ->
    spec
    (* |> List.filter (function Exists [] -> false | _ -> true) *)
    |> List.map string_of_staged_spec |> String.concat "; "

let string_of_spec_list (specs:spec list) : string = 
  match specs with 
  | [] -> "<empty disj>"
  | _ :: _ -> List.map string_of_spec specs |> String.concat " \\/ "

let string_of_disj_spec (s:disj_spec) : string = string_of_spec_list s

let string_of_pred ({ p_name; p_params; p_body } : pred_def) : string =
  Format.asprintf "%s(%s) == %s" p_name (String.concat "," p_params) (string_of_spec_list p_body)

let string_of_inclusion (lhs:spec list) (rhs:spec list) :string = 
  string_of_spec_list lhs ^" |- " ^string_of_spec_list rhs 
  ;;

let string_of_coreLang_kind (expr:core_lang): string = 
  match expr with 
  | CValue _ -> "CValue"
  | CLet  _ -> "CLet"
  | CIfELse  _ -> "CIfELse"
  | CFunCall  _ -> "CFunCall"
  | CWrite  _ -> "CWrite"
  | CRef _ -> "CRef"
  | CRead  _ -> "CRead"
  | CAssert  _ -> "CAssert"
  | CPerform  _ -> "CPerform"
  | CMatch  _ -> "CMatch"
  | CResume  _ -> "CResume"
  | CLambda  _ -> "CLambda"



let rec string_of_normalisedStagedSpec (spec:normalisedStagedSpec) : string = 
  let (effS, normalS) = spec in 
  match effS with 
  | [] -> 
    let (existiental, (p1, h1), (p2, h2), ret) = normalS in 
    let ex = match existiental with [] -> [] | _ -> [Exists existiental] in
    let current = ex @ [Require(p1, h1); NormalReturn(p2, h2, ret)] in
    string_of_spec current 
  | x :: xs  -> 
    (let {e_pre = (p1, h1); e_post = (p2, h2); _} = x in
    let ex = match x.e_evars with [] -> [] | _ -> [Exists x.e_evars] in
    let current = ex @ [Require(p1, h1);
    (match x.e_typ with
    | `Eff -> RaisingEff(p2, h2, x.e_constr, x.e_ret)
    | `Fn -> HigherOrder(p2, h2, x.e_constr, x.e_ret))] in
    string_of_spec current )
    ^ "; " ^ string_of_normalisedStagedSpec (xs, normalS)

let string_of_constr_call n args =
  match n, args with
  | "[]", _ -> "[]"
  | "::", [a1; a2] -> Format.asprintf "%s :: %s" a1 a2
  | _ -> Format.asprintf "%s(%s)" n (String.concat ", " args)

let rec string_of_core_lang (e:core_lang) :string =
  match e with
  | CValue v -> string_of_term v
  | CLet (v, e, e1) -> Format.sprintf "let %s = %s in\n%s" v (string_of_core_lang e) (string_of_core_lang e1)
  | CIfELse (i, t, e) -> Format.sprintf "if %s then %s else %s" (string_of_term i)  (string_of_core_lang t) (string_of_core_lang e)
  | CFunCall (f, [a; b]) when not (is_alpha (String.get f 0)) -> Format.sprintf "%s %s %s" (string_of_term a) f (string_of_term b)
  | CFunCall (f, xs) -> Format.sprintf "%s %s" f (List.map string_of_term xs |> String.concat " ")
  | CWrite (v, e) -> Format.sprintf "%s := %s" v (string_of_term e)
  | CRef v -> Format.sprintf "ref %s" (string_of_term v)
  | CRead v -> Format.sprintf "!%s" v
  | CAssert (p, h) -> Format.sprintf "assert (%s && %s)" (string_of_pi p) (string_of_kappa h)
  | CPerform (eff, Some arg) -> Format.sprintf "perform %s %s" eff (string_of_term arg)
  | CPerform (eff, None) -> Format.sprintf "perform %s" eff
  | CMatch (e, vs, hs, cs) -> Format.sprintf "match %s with\n%s%s\n%s" (string_of_core_lang e) (match vs with | Some (v, norm) -> Format.asprintf "| %s -> %s\n" v (string_of_core_lang norm) | _ -> "") (string_of_core_handler_ops hs) (string_of_constr_cases cs)
  | CResume v -> Format.sprintf "continue k %s" (string_of_term v)
  | CLambda (xs, spec, e) -> Format.sprintf "fun %s%s -> %s" (string_of_args Fun.id xs) (match spec with None -> "" | Some ds -> Format.asprintf "(*@ %s @*)" (string_of_disj_spec ds)) (string_of_core_lang e)

and string_of_constr_cases cs =
  cs |> List.map (fun (n, args, body) -> Format.asprintf "| %s -> %s" (string_of_constr_call n args) (string_of_core_lang body)) |> String.concat "\n"

and string_of_core_handler_ops hs =
  List.map (fun (name, v, spec, body) ->
    let spec = spec |> Option.map (fun s -> Format.asprintf "(*@@ %s @@*)" (string_of_disj_spec s)) |> Option.value ~default:"" in
    Format.asprintf "| effect %s k %s-> %s"
      (match v with None -> name | Some v -> Format.asprintf "(%s %s)" name v) (string_of_core_lang body) spec) hs |> String.concat "\n"

let string_of_effect_stage (vs, pre, post, eff, ret) =
  Format.asprintf "ex %s. req %s; ens %s /\\ %s /\\ res=%s" (String.concat " " vs) (string_of_state pre) (string_of_state post) (string_of_instant eff) (string_of_term ret)

let string_of_normal_stage (vs, pre, post, ret) =
  Format.asprintf "ex %s. req %s; ens %s /\\ res=%s" (String.concat " " vs) (string_of_state pre) (string_of_state post) (string_of_term ret)

let string_of_existentials vs = 
  match vs with
  | [] -> ""
  | _ :: _ -> Format.asprintf "ex %s. " (String.concat "," vs)

let string_of_res b = if b then green "true" else red "false"

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

let string_of_lemma l =
  Format.asprintf "%s: forall %s, %s <: %s" l.l_name (string_of_list Fun.id l.l_params) (string_of_instant l.l_left) (string_of_spec l.l_right)

(* let string_of_time = string_of_float *)
let string_of_time = Format.asprintf "%.0f"

let string_of_sset s =
  Format.asprintf "{%s}" (String.concat ", " (SSet.elements s))

let string_of_smap pp s =
  Format.asprintf "{%s}" (String.concat ", " (List.map (fun (k, v) -> Format.asprintf "%s -> %s" k (pp v)) (SMap.bindings s)))

let dbg_none = 0
let dbg_info = 1
let dbg_debug = 2
let debug_level = ref dbg_none

let debug_print title s =
  if String.length title < 6 then
    print_string (yellow title ^ " ")
  else
    print_endline (yellow title);
  print_endline s;
  if not (String.equal "" s) then print_endline ""

let debug ~title fmt =
  Format.kasprintf
    (fun s ->
      if !debug_level >= dbg_debug then (
        debug_print title s))
    fmt

let info ~title fmt =
  Format.kasprintf
    (fun s ->
      if !debug_level >= dbg_info then (
        debug_print title s))
    fmt

let conj xs =
  match xs with
  | [] -> True
  | x :: xs -> List.fold_right (fun c t -> And (c, t)) xs x

let string_of_type t =
  match t with
  | Int -> "int"
  | Unit -> "unit"
  | List_int -> "intlist"
  | Bool -> "bool"
  | TVar v -> Format.asprintf "'%s" v

let string_of_abs_env t =
  Format.asprintf "%s, %s" (string_of_smap string_of_type t.vartypes) (string_of_list (string_of_pair string_of_type string_of_type) t.eqs)

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
    ((match m.m_spec with None -> "" | Some s -> s |> List.map string_of_spec |> List.map (Format.asprintf "(*@@ %s @@*)") |> String.concat "\n\\/\n" |> fun s -> s ^ "\n"))
    (string_of_core_lang m.m_body)

let string_of_program (cp:core_program) :string =
  List.map string_of_meth_def cp.cp_methods |> String.concat "\n\n"
