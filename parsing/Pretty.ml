(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open Printf
open Types
open Z3

exception Foo of string



let verifier_counter: int ref = ref 0;;


let verifier_getAfreeVar () :string  =
  let x = "f"^string_of_int (!verifier_counter) in 
  verifier_counter := !verifier_counter + 1;
  x 
;;



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

let rule ?(children=[]) fmt = Format.kasprintf (fun s -> Node (s, children)) fmt

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
  | Var str -> str
  | Plus (t1, t2) -> string_of_term t1 ^ "+" ^ string_of_term t2
  | Minus (t1, t2) -> string_of_term t1 ^ "-" ^ string_of_term t2
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
  | Imply  (p1, p2) -> string_of_pi p1 ^ "->" ^ string_of_pi p2
  | Not    p -> "!" ^ string_of_pi p
  | Predicate (str, t) -> str ^ "(" ^ string_of_term t ^ ")"



let rec stricTcompareTerm (term1:term) (term2:term) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> String.compare s1 s2 == 0
  | (Num n1, Num n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
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

let counter : int ref = ref 0 ;;


let (historyTable: ((string * bool)list)ref) = ref [] ;;

let rec existInhistoryTable pi table= 
  match table with 
  | [] -> None
  | (x, b)::xs -> 
    if String.compare x (string_of_pi pi) == 0 then Some b 
    else existInhistoryTable pi  xs




let rec term_to_expr ctx : term -> Z3.Expr.expr = function
  | ((Num n))        -> Z3.Arithmetic.Real.mk_numeral_i ctx n
  | ((Var v))           -> Z3.Arithmetic.Real.mk_const_s ctx v
  | ((UNIT))           -> Z3.Arithmetic.Real.mk_const_s ctx "unit"
  (*
  | Gen i          -> Z3.Arithmetic.Real.mk_const_s ctx ("t" ^ string_of_int i ^ "'")
  *)
  | Plus (t1, t2)  -> Z3.Arithmetic.mk_add ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]
  | Minus (t1, t2) -> Z3.Arithmetic.mk_sub ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]
  | TList _|TTupple _ ->  failwith "term_to_expr"

let rec pi_to_expr ctx : pi -> Expr.expr = function
  | True                -> Z3.Boolean.mk_true ctx
  | False               -> Z3.Boolean.mk_false ctx
  | Atomic (GT, t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_gt ctx t1 t2
  | Atomic (GTEQ, t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_ge ctx t1 t2
  | Atomic (LT, t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_lt ctx t1 t2
  | Atomic (LTEQ, t1, t2) -> 
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      Z3.Arithmetic.mk_le ctx t1 t2
  | Atomic (EQ, t1, t2) -> 
      let newP = And (Atomic (GTEQ, t1, t2), Atomic (LTEQ, t1, t2)) in 
      pi_to_expr ctx newP
  | Imply (p1, p2) ->  pi_to_expr ctx (Or(Not p1, p2))
  | Predicate (_, _) -> failwith "pi_to_expr"
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
  | And (pi1, pi2)      -> Z3.Boolean.mk_and ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | Or (pi1, pi2)       -> Z3.Boolean.mk_or ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  (*| Imply (pi1, pi2)    -> Z3.Boolean.mk_implies ctx (pi_to_expr ctx pi1) (pi_to_expr ctx pi2)
  *)
  | Not pi              -> Z3.Boolean.mk_not ctx (pi_to_expr ctx pi)


let check ?(debug=false) ?(postprocess_expr=fun _ctx e -> e) pi =
  let cfg = [ ("model", "false"); ("proof", "false") ] in
  let ctx = mk_context cfg in
  let expr = pi_to_expr ctx pi in
  let expr = postprocess_expr ctx expr in
  if debug then Format.printf "z3: %s@." (Expr.to_string expr);
  let goal = Goal.mk_goal ctx true true false in
  (* if debug then print_endline (Goal.to_string goal); *)
  Goal.add goal [ expr ];
  let solver = Solver.mk_simple_solver ctx in
  List.iter (fun a -> Solver.add solver [ a ]) (Goal.get_formulas goal);
  let sat = Solver.check solver [] == Solver.SATISFIABLE in
  if debug then Format.printf "sat: %b@." sat;
  sat

(* this is a separate function which doesn't cache results because exists isn't in pi *)
let askZ3_exists vars pi = 
  let postprocess_expr ctx e =
    let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
    Z3.Quantifier.(expr_of_quantifier (mk_exists ctx (List.map (fun _ -> int_sort) vars) (List.map (Z3.Symbol.mk_string ctx) vars) e None [] [] None None))
  in
  check ~debug:false ~postprocess_expr pi

let askZ3 pi = 
  match existInhistoryTable pi !historyTable with 
  | Some b  -> b
  | None ->
  
  let _ = counter := !counter + 1 in 
  let re = check pi in 
  let ()= historyTable := (string_of_pi pi, re)::!historyTable in 
  
  re;;


let entailConstrains pi1 pi2 = 

  let sat = not (askZ3 (Not (Or (Not pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;

let normalPure (pi:pi):pi = 
  let allPi = getAllPi pi [] in
  let rec clear_Pi pi li = 
    (match li with 
      [] -> [pi]
    | x :: xs -> if existPi pi li then clear_Pi x xs else [pi] @ (clear_Pi x xs)
    )in 
  let finalPi = clear_Pi True allPi in
  let rec connectPi li acc = 
    (match li with 
      [] -> acc 
    | x :: xs -> if entailConstrains True x then (connectPi xs acc) else And (x, (connectPi xs acc)) 
    ) in 
  let filte_true = List.filter (fun ele-> not (comparePure ele True)  ) finalPi in 
  if List.length filte_true == 0 then  True
  else connectPi (List.tl filte_true) (List.hd filte_true)
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


let string_of_list p xs =
  match xs with
  | [] -> "[]"
  | _ ->
    let a = List.map p xs |> String.concat "; " in
    Format.asprintf "[%s]" a

let string_of_args args = string_of_list string_of_term args

let rec string_of_kappa (k:kappa) : string = 
  match k with
  | EmptyHeap -> "emp"
  | PointsTo  (str, args) -> Format.sprintf "%s->%s" str (List.map string_of_term [args] |> String.concat ", ")
  | SepConj (k1, k2) -> string_of_kappa k1 ^ "*" ^ string_of_kappa k2 
  (*| MagicWand (k1, k2) -> "(" ^ string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  ^ ")" *)
  (* | Implication (k1, k2) -> string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  *)

let string_of_state (p, h) : string =
  match h, p with
  | EmptyHeap, _ -> string_of_pi p
  | _, True -> string_of_kappa h
  | _ ->
    (* Format.asprintf "%s /\\ %s" (string_of_kappa h) (string_of_pi p) *)
    Format.asprintf "%s*%s" (string_of_kappa h) (string_of_pi p)

let string_of_stages (st:stagedSpec) : string =
  match st with
  | Require (p, h) ->
    Format.asprintf "req %s /\\ %s" (string_of_pi p) (string_of_kappa h)
  | HigherOrder (pi, h, (f, args), ret) ->
    Format.asprintf "%s /\ %s /\ %s$(%s, %s); " (string_of_pi pi) (string_of_kappa h) f (string_of_args args) (string_of_term ret)
  | NormalReturn (pi, heap, ret) ->
    Format.asprintf "Norm(%s /\\ %s, %s)" (string_of_kappa heap) (string_of_pi pi)  (string_of_term ret)
  | RaisingEff (pi, heap, (name, args), ret) ->
    Format.asprintf "%s(%s /\\ %s, %s, %s)" name (string_of_kappa heap) (string_of_pi pi)  (string_of_args args) (string_of_term ret)
  | Exists vs ->
    Format.asprintf "ex %s" (String.concat " " vs)

let string_of_spec (spec:spec) :string =
  spec |> List.map string_of_stages |> String.concat "; "

let rec string_of_spec_list (specs:spec list) : string = 
  match specs with 
  | [] -> ""
  | [x] -> string_of_spec x 
  | x :: xs -> string_of_spec x ^ " \\/ " ^ string_of_spec_list xs 

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


let rec domainOfHeap (h:kappa) : string list = 
  match h with 
  | EmptyHeap -> []
  | PointsTo (str, _) -> [str]
  | SepConj (k1, k2) -> (domainOfHeap k1) @ (domainOfHeap k2)
  (*| MagicWand (k1, k2) -> (domainOfHeap k1) @ (domainOfHeap k2) *)


let overlap domain1 domain2 : bool = 
  let rec exists str li  = 
    match li with 
    | [] -> false 
    | x :: xs -> if String.compare x str == 0 then true else exists str xs 
  in 
  let rec iterateh1 li = 
    match li with
    | [] -> false 
    | y::ys -> if exists y domain2 then true else iterateh1 ys
  in iterateh1 domain1

let domainOverlap h1 h2 = 
  let domain1 = domainOfHeap h1 in 
  let domain2 = domainOfHeap h2 in 
  overlap domain1 domain2


let () = assert (overlap ["x"] ["x"] = true)
let () = assert (overlap ["x"] ["y"] = false)
let () = assert (overlap ["x"] [] = false)

let () = assert (overlap ["x";"y"] ["y";"z"] = true )




let normaliseHeap (h) : (kappa * pi) = 
  match h with 
  | SepConj (PointsTo (s1, t1), PointsTo (s2, t2)) -> 
    if String.compare s1 s2 == 0 then (PointsTo (s1, t1), Atomic(EQ, t1, t2))
    else (h, True)
  | SepConj (EmptyHeap, h1) -> (h1, True)
  | SepConj (h1, EmptyHeap) -> (h1, True)
  | _ -> (h, True)

let mergeEns (pi1, h1) (pi2, h2) = 
  (*if domainOverlap h1 h2 then failwith "domainOverlap in mergeEns"
  else 

  *)

  
  let (heap, unification) = normaliseHeap (SepConj (h1, h2)) in 
  (*print_endline (string_of_kappa (SepConj (h1, h2)) ^ " =====> ");
  print_endline (string_of_kappa heap ^ "   and    " ^ string_of_pi unification);
*)
  (normalPure (And(And (pi1, pi2), unification)), heap)


let rec string_of_normalisedStagedSpec (spec:normalisedStagedSpec) : string = 
  let (effS, normalS) = spec in 
  match effS with 
  | [] -> 
    let (existiental, (p1, h1), (p2, h2), ret) = normalS in 
    let current = [Exists existiental; Require(p1, h1); NormalReturn(p2, h2, ret)] in 
    string_of_spec current 
  | x :: xs  -> 
    (let (existiental, (p1, h1), (p2, h2), ins, ret) = x in 
    let current = [Exists existiental; Require(p1, h1); RaisingEff(p2, h2, ins, ret)] in 
    string_of_spec current )
    ^ string_of_normalisedStagedSpec (xs, normalS) 


let rec list_of_heap h = 
   match h with 
   | EmptyHeap -> []
   | PointsTo (v, t) -> [(v, t)]
   | SepConj (h1, h2) -> list_of_heap h1 @ list_of_heap h2

(*
let rec deleteFromHeapList li (x, t1)  = 
  match li with 
  | [] -> failwith "deleteFromHeapList not found"
  | (y, t2)::ys -> if String.compare x y == 0 && stricTcompareTerm t1 t2 then ys
    else (y, t2):: (deleteFromHeapList ys (x, t1))


(* the accumption is h1 |- h2 ~~~~> r, and return r *)
let getheapResidue h1 h2 : kappa =  
  let listOfHeap1 = list_of_heap h1 in 
  let listOfHeap2 = list_of_heap h2 in 
  let rec helper acc li = 
    match li with 
    | [] -> acc 
    | (x, v) :: xs  -> 
      let acc' = deleteFromHeapList acc (x, v) in 
      helper acc' xs
  in 
  let temp = helper listOfHeap1 listOfHeap2  in 
  kappa_of_list temp 

*)

let rec kappa_of_list li = 
  match li with 
  | [] -> EmptyHeap 
  | (x, v)::xs ->  SepConj (PointsTo (x, v), kappa_of_list xs)


  
let rec deleteFromHeapListIfHas li (x, t1) : (((string * term) list) *pi) = 
  match li with 
  | [] -> ([], True)
  | (y, t2)::ys -> 
    if String.compare x y == 0 then 
      if stricTcompareTerm t1 t2 
          || stricTcompareTerm t1 (Var "_") 
          || stricTcompareTerm t2 (Var "_") 
      then (ys, True)
      else (ys, Atomic (EQ, t1, t2))
    else 
      let (res, uni) = (deleteFromHeapListIfHas ys (x, t1)) in 
      ((y, t2):: res, uni)
      


(* h1 * h |- h2, returns h and unificiation *)
let normaliseMagicWand  h1 h2 : (kappa * pi) = 
  let listOfHeap1 = list_of_heap h1 in 
  let listOfHeap2 = list_of_heap h2 in 
  let rec helper (acc:(((string * term) list) *pi)) li = 
    let (heapLi, unification) = acc in 
    match li with 
    | [] -> acc 
    | (x, v) :: xs  -> 
      let (heapLi', unification')  = deleteFromHeapListIfHas heapLi (x, v) in 
      helper (heapLi', And (unification, unification')) xs
  in 
  let (temp, unifinication) = helper (listOfHeap2, True) listOfHeap1  in 
  (kappa_of_list temp , unifinication)


  


let normalise_stagedSpec (acc:normalisedStagedSpec) (stagedSpec:stagedSpec) : normalisedStagedSpec = 
  (*print_endline("\nnormalise_stagedSpec =====> " ^ string_of_normalisedStagedSpec(acc));
  print_endline("\nadding  " ^ string_of_stages (stagedSpec));
*)

  let (effectStages, normalStage) = acc in 
  let (existential, req, ens, ret) = normalStage in 
  match stagedSpec with
  | Exists li -> (effectStages, (existential@li, req, ens, ret))
  | Require (pi, heap) -> 
    let (p2, h2) = ens in 
    let (magicWandHeap, unification) = normaliseMagicWand h2 heap in 
    (*print_endline (string_of_kappa (magicWandHeap) ^ " magic Wand "); *)

    (* not only need to get the magic wand, but also need to delete the common part from h2*)
    let (h2',   unification')    = normaliseMagicWand heap h2 in 

    let normalStage' = (existential, mergeEns req (And(pi, unification), magicWandHeap), (normalPure (And(p2, unification')), h2'), ret) in 
    (effectStages, normalStage')

  | NormalReturn (pi, heap, ret') -> (effectStages, (existential, req, mergeEns ens (pi, heap), ret'))
  (* effects *)
  | RaisingEff (pi, heap,ins, ret') -> 
    (effectStages@[(existential, req, mergeEns ens (pi, heap), ins , ret')], freshNoramlStage)
  (* higher-order functions *)
  | HigherOrder (pi, heap, ins, ret') ->
    (* same as RaisingEff *)
    (effectStages@[(existential, req, mergeEns ens (pi, heap), ins , ret')], freshNoramlStage)

let rec normalise_spec (acc:normalisedStagedSpec) (spec:spec) : normalisedStagedSpec = 
  match spec with 
  | [] -> acc 
  | x :: xs -> 
    let acc' = normalise_stagedSpec acc x in 
    normalise_spec acc' xs 

let rec effectStage2Spec (effectStages:effectStage list ) : spec = 
  match effectStages with
  | [] -> []
  | (existiental, (p1, h1), (p2, h2), ins, ret) :: xs  -> 
    (match existiental with 
    | [] -> [] 
    | _ -> [Exists existiental])
    @
    (match (p1, h1) with 
    | (True, EmptyHeap) -> []
    | _ -> [Require(p1, h1)])
    @
    ([RaisingEff(p2, h2, ins, ret)])
    @ effectStage2Spec xs 

let normalStage2Spec (normalStage:normalStage ) : spec = 
  let (existiental, (p1, h1), (p2, h2), ret) = normalStage in 
  (match existiental with 
  | [] -> [] 
  | _ -> [Exists existiental])
  @
  (match (p1, h1) with 
  | (True, EmptyHeap) -> []
  | _ -> [Require(p1, h1)])
  @
  (match (p2, h2, ret) with 
  | (True, EmptyHeap, UNIT) -> []
  | _ -> [NormalReturn(p2, h2, ret)])

let rec detectfailedAssertions (spec:spec) : spec = 
  match spec with 
  | [] -> []
  | Require (pi, heap) :: xs  -> 
    (
      let pi' = normalPure pi in 
      match entailConstrains pi' (False) with 
      | true  -> [Require (False , heap)]
      | _ -> Require (pi' , heap) ::  detectfailedAssertions xs 
    )
  (* higher-order functions *)
  | x :: xs -> x :: detectfailedAssertions xs 



let normalisedStagedSpec2Spec (normalisedStagedSpec:normalisedStagedSpec) : spec  = 
  let (effS, normalS) = normalisedStagedSpec in 
  detectfailedAssertions (effectStage2Spec effS @ normalStage2Spec normalS)


let normalise_spec_list (specLi:spec list): spec list = 
  List.map (fun a -> 
    let normalisedStagedSpec = normalise_spec ([], freshNoramlStage) a in 
    normalisedStagedSpec2Spec normalisedStagedSpec
    
  ) specLi



