(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open Printf
open Hiptypes

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


let verifier_getAfreeVar ?from () :string  =
  let prefix = from |> Option.map (fun v -> v ^ "_") |> Option.value ~default:"_f" in
  let x = prefix ^ ""^string_of_int (!verifier_counter) in 
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
  | Imply  (p1, p2) -> string_of_pi p1 ^ "=>" ^ string_of_pi p2
  | Not    p -> "!" ^ string_of_pi p
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


let string_of_pair pa pb (a,b) =
  Format.asprintf "(%s, %s)" (pa a) (pb b)

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
    Format.asprintf "%s$(%s, %s, %s)" f (string_of_state (pi, h)) (string_of_args args) (string_of_term ret)
  | NormalReturn (pi, heap, ret) ->
    Format.asprintf "Norm(%s, %s)" (string_of_state (pi, heap))  (string_of_term ret)
  | RaisingEff (pi, heap, (name, args), ret) ->
    Format.asprintf "%s(%s, %s, %s)" name (string_of_state (pi, heap)) (string_of_args args) (string_of_term ret)
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


let rec domainOfHeap (h:kappa) : string list = 
  match h with 
  | EmptyHeap -> []
  | PointsTo (str, _) -> [str]
  | SepConj (k1, k2) -> (domainOfHeap k1) @ (domainOfHeap k2)
  (*| MagicWand (k1, k2) -> (domainOfHeap k1) @ (domainOfHeap k2) *)


let rec existStr str li  = 
    match li with 
    | [] -> false 
    | x :: xs -> if String.compare x str == 0 then true else existStr str xs 


let overlap domain1 domain2 : bool = 
  let rec iterateh1 li = 
    match li with
    | [] -> false 
    | y::ys -> if existStr y domain2 then true else iterateh1 ys
  in iterateh1 domain1

let domainOverlap h1 h2 = 
  let domain1 = domainOfHeap h1 in 
  let domain2 = domainOfHeap h2 in 
  overlap domain1 domain2


let () = assert (overlap ["x"] ["x"] = true)
let () = assert (overlap ["x"] ["y"] = false)
let () = assert (overlap ["x"] [] = false)

let () = assert (overlap ["x";"y"] ["y";"z"] = true )




let rec normaliseHeap (h) : (kappa) = 
  match h with 
  (*
  | SepConj (PointsTo (s1, t1), PointsTo (s2, t2)) -> 
    if String.compare s1 s2 == 0 then (PointsTo (s1, t1), Atomic(EQ, t1, t2))
    else (h, True)
  *)
  | SepConj (EmptyHeap, h1) -> (normaliseHeap h1)
  | SepConj (h1, EmptyHeap) -> (normaliseHeap h1)
  | _ -> (h)

let mergeState (pi1, h1) (pi2, h2) = 
  
  let (heap) = normaliseHeap (SepConj (h1, h2)) in 
  (*print_endline (string_of_kappa (SepConj (h1, h2)) ^ " =====> ");
  print_endline (string_of_kappa heap ^ "   and    " ^ string_of_pi unification);
*)
  (ProversEx.normalize_pure (And (pi1, pi2)), heap)


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
    let current = ex @ [Require(p1, h1); RaisingEff(p2, h2, x.e_constr, x.e_ret)] in
    string_of_spec current )
    ^ "; " ^ string_of_normalisedStagedSpec (xs, normalS)


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


(* (x, t1) -* (y, t2) *)  
let rec deleteFromHeapListIfHas li (x, t1) existential flag: (((string * term) list) *pi) = 
  match li with 
  | [] -> ([], True)
  | (y, t2)::ys -> 
    if String.compare x y == 0 then 
      if stricTcompareTerm t2 (Var "_") then (ys, True)
      else 
      match (t1, t2) with 
      (* x->11 -* x-> z   ~~~>   (emp, true) *)
      | (Num _, Var t2Str) ->  
        if existStr t2Str existential then (ys, True)
        else (ys, Atomic (EQ, t1, t2))
      (* x-> z -* x-> 11   ~~~>  (emp, z=11) *)
      | (Var t2Str, Num _) ->  
        if String.compare t2Str "_" == 0
        then (ys, True)
        else (ys, Atomic (EQ, t1, t2))
      | (_, _) -> 
        if stricTcompareTerm t1 t2 || stricTcompareTerm t1 (Var "_") 
        then (ys, True)
        else 
          if flag then (ys, Atomic (EQ, t1, t2) )
          else (ys, Atomic (EQ, t1, t2) )
    else 
      let (res, uni) = (deleteFromHeapListIfHas ys (x, t1) existential) flag in 
      ((y, t2):: res, uni)
      


(* h1 * h |- h2, returns h and unificiation 
x -> 3 |- x -> z   -> (emp, true )
x -> z |- x -> 3   -> (emp, z = 3)
*)
let normaliseMagicWand  h1 h2 existential flag: (kappa * pi) = 
  let listOfHeap1 = list_of_heap h1 in 
  let listOfHeap2 = list_of_heap h2 in 
  let rec helper (acc:(((string * term) list) * pi)) li = 
    let (heapLi, unification) = acc in 
    match li with 
    | [] -> acc 
    | (x, v) :: xs  -> 
      let (heapLi', unification')  = deleteFromHeapListIfHas heapLi (x, v) existential flag in 
      helper (heapLi', And (unification, unification')) xs
  in 
  let (temp, unifinication) = helper (listOfHeap2, True) listOfHeap1  in 
  (normaliseHeap (kappa_of_list temp) , unifinication)



let normalise_stagedSpec (acc:normalisedStagedSpec) (stagedSpec:stagedSpec) : normalisedStagedSpec = 
  (*print_endline("\nnormalise_stagedSpec =====> " ^ string_of_normalisedStagedSpec(acc));
  print_endline("\nadding  " ^ string_of_stages (stagedSpec));
*)
  let (effectStages, normalStage) = acc in 
  let (existential, req, ens, ret) = normalStage in 
  match stagedSpec with
  | Exists li -> (effectStages, (existential@li, req, ens, ret))
  | Require (p3, h3) -> 
    let (p2, h2) = ens in 
    let (magicWandHeap, unification) = normaliseMagicWand h2 h3 existential true in 
    (*print_endline (string_of_kappa (magicWandHeap) ^ " magic Wand "); *)

    (* not only need to get the magic wand, but also need to delete the common part from h2*)
    let (h2',   unification')    = normaliseMagicWand h3 h2 existential false in 


    let normalStage' = (existential, mergeState req (And(p3, unification), magicWandHeap), (ProversEx.normalize_pure (And(p2, unification')), h2'), ret) in 
    (effectStages, normalStage')

  | NormalReturn (pi, heap, ret') ->
    (effectStages, (existential, req, mergeState ens (pi, heap), ret'))
  (* effects *)
  | RaisingEff (pi, heap,ins, ret') -> 
    (* move current norm state "behind" this effect boundary. the return value is implicitly that of the current stage *)
    (effectStages@[{e_evars = existential; e_pre = req; e_post = mergeState ens (pi, heap); e_constr = ins ; e_ret = ret'; e_typ = `Eff}], freshNormStageRet ret')
  (* higher-order functions *)
  | HigherOrder (pi, heap, ins, ret') ->
    (effectStages@[{e_evars = existential; e_pre = req; e_post = mergeState ens (pi, heap); e_constr = ins ; e_ret = ret'; e_typ = `Fn}], freshNormStageRet ret')
  (* | IndPred {name; _} -> *)
    (* failwith (Format.asprintf "cannot normalise predicate %s" name) *)

let (*rec*) normalise_spec_ (acc:normalisedStagedSpec) (spec:spec) : normalisedStagedSpec =
  List.fold_left normalise_stagedSpec acc spec
  (* match spec with
  | [] -> acc 
  | x :: xs -> 
    (*let time_1 = Sys.time() in*)
    let acc' = normalise_stagedSpec acc x in 
    (*let time_2 = Sys.time() in
    let during = time_2 -. time_1 in 
    (
    print_endline (string_of_stages x );
    print_endline ("[testing   Time] " ^ string_of_float ((during) *. 1000.0) ^ " ms\n"));
*)
    normalise_spec_ acc' xs  *)

let rec used_vars_term (t : term) =
  match t with
  | UNIT | Num _ -> []
  | TList ts | TTupple ts -> List.concat_map used_vars_term ts
  | Var s -> [s]
  | Plus (a, b) | Minus (a, b) -> used_vars_term a @ used_vars_term b

let rec used_vars_pi (p : pi) =
  match p with
  | True | False -> []
  | Atomic (_, a, b) -> used_vars_term a @ used_vars_term b
  | And (a, b) | Or (a, b) | Imply (a, b) -> used_vars_pi a @ used_vars_pi b
  | Not a -> used_vars_pi a
  | Predicate (_, t) -> used_vars_term t

let rec used_vars_heap (h : kappa) =
  match h with
  | EmptyHeap -> []
  | PointsTo (a, t) -> a :: used_vars_term t
  | SepConj (a, b) -> used_vars_heap a @ used_vars_heap b

let used_vars_state (p, h) = used_vars_pi p @ used_vars_heap h

let used_vars_eff eff =
  used_vars_state eff.e_pre @ used_vars_state eff.e_post
  @ List.concat_map used_vars_term (snd eff.e_constr)
  @ used_vars_term eff.e_ret

let used_vars_norm (_vs, pre, post, ret) =
  used_vars_state pre @ used_vars_state post @ used_vars_term ret

let used_vars (sp : normalisedStagedSpec) =
  let effs, norm = sp in
  List.concat_map used_vars_eff effs @ used_vars_norm norm
  |> List.sort_uniq String.compare

let remove_redundant_vars : normalisedStagedSpec -> normalisedStagedSpec = fun sp1 ->
  let sp2 =
    let used = used_vars sp1 in
    let effs, norm = sp1 in
    let norm1 =
      let vs, pre, post, ret = norm in
      (List.filter (fun a -> List.mem a used) vs, pre, post, ret)
    in
    let effs1 =
      List.map
        (fun eff ->
          { eff with e_evars = List.filter (fun a -> List.mem a used) eff.e_evars })
        effs
    in
    (effs1, norm1)
  in
  sp2

(* this moves existentials inward and removes unused ones *)
let optimize_existentials : normalisedStagedSpec -> normalisedStagedSpec = fun (ess, norm) ->
  let rec loop unused acc es =
    match es with
    | [] -> unused, List.rev acc
    | e :: rest ->
      let used = used_vars_eff e in
      let may_be_used = e.e_evars @ unused in
      let used_ex, unused_ex = List.partition (fun v -> List.mem v used) may_be_used in
      loop (unused_ex @ unused) ({ e with e_evars = used_ex } :: acc) rest
  in
  let unused, es1 = loop [] [] ess in
  let norm1 =
      let used = used_vars_norm norm in
      let (evars, h, p, r) = norm in
      let may_be_used = evars @ unused in
      (* unused ones are dropped *)
      let used_ex, _unused_ex = List.partition (fun v -> List.mem v used) may_be_used in
      (used_ex, h, p, r)
  in
  (es1, norm1)

let normalise_spec sp =
  let v = verifier_getAfreeVar ~from:"n" () in
  let acc = ([], freshNormStageVar v) in
  let sp1 = normalise_spec_ acc sp in
  sp1
  (* redundant vars may appear due to fresh stages *)
  |> optimize_existentials

let rec effectStage2Spec (effectStages:effectStage list ) : spec = 
  match effectStages with
  | [] -> []
  | eff :: xs ->
    let p2, h2 = eff.e_post in
    (match eff.e_evars with 
    | [] -> [] 
    | _ -> [Exists eff.e_evars])
    @
    (match eff.e_pre with 
    | (True, EmptyHeap) -> []
    | (p1, h1) -> [Require(p1, h1)])
    @
    [match eff.e_typ with
    | `Eff -> RaisingEff(p2, h2, eff.e_constr, eff.e_ret)
    | `Fn -> HigherOrder(p2, h2, eff.e_constr, eff.e_ret)]
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
  (*| (True, EmptyHeap, UNIT) -> [] *)
  | _ -> [NormalReturn(p2, h2, ret)])

let rec detectfailedAssertions (spec:spec) : spec = 
  match spec with 
  | [] -> []
  | Require (pi, heap) :: xs  -> 
    (
      let pi' = ProversEx.normalize_pure pi in 
      match ProversEx.entailConstrains pi' (False) with 
      | true  -> [Require (False , heap)]
      | _ -> Require (pi' , heap) ::  detectfailedAssertions xs 
    )
  (* higher-order functions *)
  | x :: xs -> x :: detectfailedAssertions xs 



let normalisedStagedSpec2Spec (normalisedStagedSpec:normalisedStagedSpec) : spec  = 
  let (effS, normalS) = normalisedStagedSpec in 
  detectfailedAssertions (effectStage2Spec effS @ normalStage2Spec normalS)

let normalise_spec_list_aux1 (specLi:spec list): normalisedStagedSpec list = 
  List.map (fun a -> normalise_spec a
  ) specLi

let normalise_spec_list_aux2 (specLi:normalisedStagedSpec list): spec list = 
  List.map (fun a -> normalisedStagedSpec2Spec a
  ) specLi


let normalise_spec_list (specLi:spec list): spec list = 
  List.map (fun a -> 
    let normalisedStagedSpec = normalise_spec a in 
    normalisedStagedSpec2Spec normalisedStagedSpec
    
  ) specLi


let rec deleteFromStringList str (li:string list) = 
  match li with 
  | [] -> [] 
  | x ::xs -> if String.compare x str == 0 then xs 
    else x :: deleteFromStringList str xs

let removeExist (specs:spec list) str : spec list =
  (*print_endline ("removeExist ===>   " ^ str );
  *)
  let aux (stage:stagedSpec): stagedSpec = 
    match stage with 
    | Exists strli -> 
      Exists (deleteFromStringList str strli)
    | _ -> stage
  in 
  let helper (spec:spec) : spec = 
    List.map (fun a -> aux a) spec 
  in 
  List.map (fun a -> helper a) specs



let%expect_test "normalise spec" =
  verifier_counter_reset ();
  let test s =
    let n = normalise_spec s in
    Format.printf "%s\n==>\n%s\n@." (string_of_spec s) (string_of_normalisedStagedSpec n)
  in
  print_endline "--- norm\n";
  test [
    NormalReturn (True, PointsTo ("x", Num 2), UNIT);
    Require (True, PointsTo("x", Num 1)) ];
  test [
    Require (True, PointsTo("x", Num 1));
    NormalReturn (True, PointsTo ("x", Num 1), UNIT);
    Require (True, PointsTo("y", Num 2));
    NormalReturn (True, PointsTo ("y", Num 2), UNIT) ];
  test [
    NormalReturn (True, PointsTo ("x", Num 1), UNIT);
    Require (True, PointsTo("x", Var "a"));
    NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), UNIT) ];
  test [
    NormalReturn (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2)), UNIT);
    Require (True, PointsTo("x", Var "a"));
    NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), UNIT)
    ];
  test [
    NormalReturn (Atomic(EQ, Var"a", Num 3), (PointsTo ("y", Var "a")), UNIT);
    Require (Atomic(EQ, Var "b", Var "a"), PointsTo("x", Var "b"));
    NormalReturn (True, PointsTo ("x", Plus (Var "b", Num 1)), UNIT)
    ];
  print_endline "--- eff\n";
  test [
    NormalReturn (True, PointsTo ("x", Num 1), UNIT);
    Require (True, PointsTo("x", Var "1"));
    RaisingEff (True, PointsTo ("x", Num 1), ("E", [Num 3]), UNIT);
    NormalReturn (True, PointsTo ("y", Num 2), UNIT) ];
  test [
    NormalReturn (True, PointsTo ("x", Num 1), UNIT);
    HigherOrder (True, EmptyHeap, ("f", [Num 3]), UNIT);
    NormalReturn (True, PointsTo ("y", Num 2), UNIT) ];
[%expect
{|
  --- norm

  Norm(x->2, ()); req x->1
  ==>
  req 2=1; Norm(1=2, ())

  req x->1; Norm(x->1, ()); req y->2; Norm(y->2, ())
  ==>
  req x->1*y->2; Norm(x->1*y->2, ())

  Norm(x->1, ()); req x->a; Norm(x->a+1, ())
  ==>
  req 1=a; Norm(x->a+1 /\ a=1, ())

  Norm(x->1*y->2, ()); req x->a; Norm(x->a+1, ())
  ==>
  req 1=a; Norm(y->2*x->a+1 /\ a=1, ())

  Norm(y->a /\ a=3, ()); req x->b /\ b=a; Norm(x->b+1, ())
  ==>
  req x->b /\ b=a; Norm(y->a*x->b+1 /\ a=3, ())

  --- eff

  Norm(x->1, ()); req x->1; E(x->1, [3], ()); Norm(y->2, ())
  ==>
  req 1=1; E(x->1 /\ 1=1, [3], ()); req emp; Norm(y->2, ())

  Norm(x->1, ()); f$(emp, [3], ()); Norm(y->2, ())
  ==>
  req emp; f(x->1, [3], ()); req emp; Norm(y->2, ())
|}]

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

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
  | CMatch (e, (v, norm), hs) -> Format.sprintf "match %s with\n| %s -> %s\n%s" (string_of_core_lang e) v (string_of_core_lang norm) (List.map (fun (name, v, body) -> Format.asprintf "| effect %s k -> %s" (match v with None -> name | Some v -> Format.asprintf "(%s %s)" name v) (string_of_core_lang body)) hs |> String.concat "\n")
  | CResume v -> Format.sprintf "continue k %s" (string_of_term v)

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