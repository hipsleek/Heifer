(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open Printf
open Parsetree


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

let compareBasic (p1:basic_t) (p2:basic_t) :bool = 
  match (p1, p2) with 
  | (BINT x, BINT y) -> x = y
  | (UNIT, UNIT) -> true
  | (VARName s1, VARName s2) -> String.compare s1 s2 == 0

  | _ -> false

let compareParm (p1:basic_t list) (p2:basic_t list) :bool = 
  List.equal compareBasic p1 p2

let compareInstant ( (n1, a1)) ( (n2, a2)) :bool = 
  String.equal n1 n2 && compareParm a1 a2
  



let string_of_bin_op op : string =
  match op with 
  | GT -> ">" 
  | LT -> "<" 
  | EQ -> "=" 
  | GTEQ -> ">="
  | LTEQ -> "<="



let rec normalPure p = 
  match p with
  | And (True, p1) -> normalPure p1
  | And (p1, True) -> normalPure p1
  | And (p1, p2) -> And (normalPure p1, normalPure p2)
  | _ -> p 
;;




let rec kappaToPure kappa : pi =
  match kappa with 
  | EmptyHeap -> True
  | PointsTo (str, t) -> Atomic(EQ, Var str, t)
  | SepConj (k1, k2) -> And (kappaToPure k1, kappaToPure k2)
  | MagicWand (_, _) -> failwith "kappaToPure unimplemented"

  (* | Implication (k1, k2) -> Imply (kappaToPure k1, kappaToPure k2) *)

 
let basic_t2Term (a) : term = 
  match a with 
  | BINT i -> Num i 
  | VARName s -> Var s
  | List s -> TList (List.map (fun a -> Num a) s )
  | _ -> failwith "basic_t2Term"
     


let string_of_basic_type a : string = 
  match a with 
  | BINT i -> string_of_int i 
  | UNIT -> "()"
  | VARName s -> s
  | List s ->
    Format.asprintf "[%s]"
      (List.map string_of_int s |> String.concat "; ")

let string_of_instant (str, ar_Li): string = 
  (* syntax is like OCaml type constructors, e.g. Foo, Foo (), Foo (1, ()) *)
  let args =
    match ar_Li with
    | [] -> ""
    | [t] -> Format.sprintf "(%s)" (string_of_basic_type t)
    | _ -> Format.sprintf "(%s)" (separate (ar_Li) (string_of_basic_type) (","));
  in
  Format.sprintf "%s%s" str args


let string_of_args args =
  List.map string_of_basic_type args |> String.concat ", "

let rec string_of_term t : string = 
  match t with 
  | Num i -> string_of_int i 
  | Var str -> str
  | Plus (t1, t2) -> string_of_term t1 ^ " + " ^ string_of_term t2
  | Minus (t1, t2) -> string_of_term t1 ^ " - " ^ string_of_term t2
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

let rec string_of_kappa (k:kappa) : string = 
  match k with
  | EmptyHeap -> "emp"
  | PointsTo  (str, args) -> Format.sprintf "%s->%s" str (List.map string_of_term [args] |> String.concat ", ")
  | SepConj (k1, k2) -> string_of_kappa k1 ^ "*" ^ string_of_kappa k2 
  | MagicWand (k1, k2) -> string_of_kappa k1 ^ "-*" ^ string_of_kappa k2 
  (* | Implication (k1, k2) -> string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  *)

let rec string_of_pi pi : string = 
  match pi with 
  | True -> "true"
  | False -> "false"
  | Atomic (op, t1, t2) -> string_of_term t1 ^ string_of_bin_op op ^ string_of_term t2
  | And   (p1, p2) -> string_of_pi p1 ^ "/\\" ^ string_of_pi p2
  | Or     (p1, p2) -> string_of_pi p1 ^ "\\/" ^ string_of_pi p2
  | Imply  (p1, p2) -> string_of_pi p1 ^ "->" ^ string_of_pi p2
  | Not    p -> "!" ^ string_of_pi p
  | Predicate (str, t) -> str ^ "(" ^ string_of_term t ^ ")"

let string_of_stages (st:stagedSpec) : string =
  match st with
  | Require (p, h) ->
    Format.asprintf "req %s /\\ %s" (string_of_pi p) (string_of_kappa h)
  | HigherOrder (f, args) ->
    Format.asprintf "%s$(%s)" f (string_of_args args)
  | NormalReturn (pi, heap, ret) ->
    Format.asprintf "Norm(%s, %s,  %s)" (string_of_kappa heap) (string_of_pi pi)  (string_of_basic_type ret) (*string_of_args args*)
  | RaisingEff (pi, heap, (name, args), ret) ->
    Format.asprintf "%s(%s, %s, %s, %s)" name (string_of_kappa heap) (string_of_pi pi)  (string_of_args args) (string_of_basic_type ret)
  | Exists vs ->
    Format.asprintf "ex %s" (String.concat " " vs)

let string_of_spec (spec:spec) :string =
  spec |> List.map string_of_stages |> String.concat "; "


let string_of_inclusion (lhs:spec) (rhs:spec) :string = 
  string_of_spec lhs ^" |- " ^string_of_spec rhs 
  ;;
