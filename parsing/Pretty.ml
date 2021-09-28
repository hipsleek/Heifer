(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open Printf
open Parsetree


exception Foo of string


(*used to generate the free veriables, for subsititution*)
let freeVar = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
              ;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
              ;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;



let getAfreeVar (varList:string list):string  =
  let rec findOne li = 
    match li with 
        [] -> raise ( Foo "freeVar list too small exception!")
      | x :: xs -> if (List.exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
  in
  findOne freeVar
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

let rec compareParm (p1:basic_t list) (p2:basic_t list) :bool = 
  match (p1, p2) with 
  | ([], []) -> true 
  | (BINT x::xs, BINT y::ys) -> x == y  && compareParm xs ys
  | (UNIT::xs, UNIT::ys) ->  compareParm xs ys
  | _ -> false
  ;;

let compareEvent (ev1:event) (ev2:event): bool =
  match (ev1, ev2) with 
  | (Any, _) -> true 
  | (_, Any) -> true 
  | (One (str1), One (str2)) -> 
    String.compare str1 str2 == 0 (* && compareParm parms1 parms2 *)
  | (Zero (str1), Zero (str2)) -> 
  String.compare str1 str2 == 0 (* && compareParm parms1 parms2 *)
  | (Pred (str1, parms1), Pred (str2, parms2)) -> 
  String.compare str1 str2 == 0  && compareParm parms1 parms2

  | _ -> false 

  ;;

let string_of_basic_type a : string = 
  match a with 
  | BINT i -> string_of_int i 
  | UNIT -> "()"

let string_of_instant (str, ar_Li): string = 
  (* syntax is like OCaml type constructors, e.g. Foo, Foo (), Foo (1, ()) *)
  let args =
    match ar_Li with
    | [] -> ""
    | [t] -> " " ^ string_of_basic_type t
    | _ -> Format.sprintf " (%s)" (separate (ar_Li) (string_of_basic_type) (","));
  in
  Format.sprintf "%s%s" str args

  
let rec string_of_es es : string = 
  match es with 
  | Bot -> "_|_"
  | Emp -> "emp"
  | Predicate ins  -> Format.sprintf "Q(%s)" (string_of_instant ins)
  | Event str -> str
  | Not str -> "!" ^ str
  | Cons (es1, es2) -> string_of_es es1 ^"."^ string_of_es es2 
  | ESOr (es1, es2) -> string_of_es es1 ^"+"^ string_of_es es2 
  | Kleene es1 -> "("^string_of_es es1^")^*"
  | Omega es1 -> "("^string_of_es es1^")^w"
  | Underline -> "_"
  ;;

let rec string_of_term t : string = 
  match t with 
  | Num i -> string_of_int i 
  | Var str -> str
  | Plus (t1, t2) -> string_of_term t1 ^ " + " ^ string_of_term t2
  | Minus (t1, t2) -> string_of_term t1 ^ " - " ^ string_of_term t2

let string_of_bin_op op : string =
  match op with 
  | GT -> ">" 
  | LT -> "<" 
  | EQ -> "=" 
  | GTEQ -> ">="
  | LTEQ -> "<="

let string_of_side side : string =
  side
    |> List.map (fun (ins, (es1, es2)) ->
      Format.sprintf "eff(%s) = %s -> %s" 
        ins
        (string_of_es es1)
        (string_of_es es2) )
    |> String.concat ", "

let rec string_of_pi pi : string = 
  match pi with 
  | True -> "true"
  | False -> "false"
  | Atomic (op, t1, t2) -> string_of_term t1 ^ string_of_bin_op op ^ string_of_term t2
  | And   (p1, p2) -> string_of_pi p1 ^ "/\\" ^ string_of_pi p2
  | Or     (p1, p2) -> string_of_pi p1 ^ "\\/" ^ string_of_pi p2
  | Imply  (p1, p2) -> string_of_pi p1 ^ "->" ^ string_of_pi p2
  | Not    p -> "!" ^ string_of_pi p



let string_of_spec (_ (*pi*), es, side) =
  let side =
    match side with
    | [] -> ""
    | _ -> ", " ^ string_of_side side
  in
  Format.sprintf "%s%s"
    (*(string_of_pi pi)*) (string_of_es es) side



let string_of_inclusion (lhs:es) (rhs:es) :string = 
  string_of_es lhs ^" |- " ^string_of_es rhs 
  ;;

let rec normalES (es:es):es = 
  match es with
  | Bot -> es
  | Emp -> es
  | Event _ -> es
  | Not _ -> es 
  | Underline -> es
  | Predicate _ -> es 

  | Cons (Cons (esIn1, esIn2), es2)-> 
    normalES (Cons (esIn1, normalES (Cons (esIn2, es2)))) 
    
  | Cons (es1, es2) ->  
      let normalES1 = normalES es1 in
      let normalES2 = normalES es2 in
      (match (normalES1, normalES2) with 
        (Emp, _) -> normalES2 
      | (_, Emp) -> normalES1
      | (Bot, _) -> Bot
      | (Omega _, _ ) -> normalES1

      | (normal_es1, normal_es2) -> Cons (normal_es1, normal_es2)
      ;)
  | ESOr (es1, es2) -> 
      (match (normalES es1  , normalES es2  ) with 
        (Bot, Bot) -> Bot
      | (Bot, norml_es2) -> norml_es2
      | (norml_es1, Bot) -> norml_es1
      | (ESOr(es1In, es2In), norml_es2 ) ->
        ESOr (ESOr(es1In, es2In), norml_es2 )
      | (norml_es2, ESOr(es1In, es2In) ) ->
        ESOr (norml_es2, ESOr(es1In, es2In))
      | (Emp, Kleene norml_es2) ->  Kleene norml_es2
      | (Kleene norml_es2, Emp) ->  Kleene norml_es2

      | (norml_es1, norml_es2) -> ESOr (norml_es1, norml_es2)
      ;)

  | Omega es1 -> 
      let normalInside = normalES es1 in 
      (match normalInside with
        Emp -> Emp
      | _ ->  Omega normalInside)
  | Kleene es1 -> 
      let normalInside = normalES es1 in 
      (match normalInside with
        Emp -> Emp
      | Kleene esIn1 ->  Kleene (normalES esIn1  )
      | ESOr(Emp, aa) -> Kleene aa
      | _ ->  Kleene normalInside)



  ;;


let normalSide s = s
let normalPure p = p

let normalSpec (pi, es, side) : spec = (normalPure pi, normalES es, normalSide side)


let eventToEs ev : es =
  match ev with 
  | One ins -> Event ins 
  | Zero ins -> Not ins
  | Pred ins -> Predicate ins
  | Any -> Underline

  ;;


(* let rec string_of_event ev : string =
  match ev with 
  | One (str) ->  str (*^ "(" ^ separate (ar_Li) (string_of_int) (",") ^")" *)
  | Zero (str) -> "!" ^ string_of_event (One (str))
  | Pred (str, ar_Li) -> "Q(" ^str ^  separate (ar_Li) (string_of_basic_type) (",") ^")" 
  | Any -> "_" *)

  ;;

let rec string_of_policies ps: string = 
  match ps with 
  | [] -> ""
  | x::xs -> 
    (match x with 
    | Eff (str, es) -> "Effect "^ str ^ " -> " ^ string_of_es (es) ^ "\n"
    | Exn str -> "Exeption " ^ str 
    ) ^ string_of_policies xs 