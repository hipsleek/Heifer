(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open List
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
      | x :: xs -> if (exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
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

let rec compareParm (p1:int list) (p2:int list) :bool = 
  match (p1, p2) with 
  | ([], []) -> true 
  | (x::xs, y::ys) -> x == y  && compareParm xs ys
  | _ -> false
  ;;

let compareEvent (ev1:event) (ev2:event): bool =
  match (ev1, ev2) with 
  | (Any, _) -> true 
  | (_, Any) -> true 
  | (One (str1, parms1), One (str2, parms2)) -> 
    String.compare str1 str2 == 0 && compareParm parms1 parms2
  | (Zero (str1, parms1), Zero (str2, parms2)) -> 
  String.compare str1 str2 == 0 && compareParm parms1 parms2
  | _ -> false 

  ;;

  
let rec string_of_es es : string = 
  match es with 
  | Bot -> "_|_"
  | Emp -> "emp"
  | Event (str, ar_Li) -> str ^ "(" ^ separate (ar_Li) (string_of_int) (",") ^")"
  | Not (str, ar_Li) -> "!" ^ string_of_es (Event (str, ar_Li))
  | Cons (es1, es2) -> string_of_es es1 ^"."^ string_of_es es2 
  | ESOr (es1, es2) -> string_of_es es1 ^"+"^ string_of_es es2 
  | Kleene es1 -> "("^string_of_es es1^")^*"
  | Omega es1 -> "("^string_of_es es1^")^w"
  | Underline -> "_"
  ;;

let string_of_inclusion (lhs:es) (rhs:es) :string = 
  string_of_es lhs ^" |- " ^string_of_es rhs 
  ;;

let rec normalES (es:es):es = 
  match es with
    Bot -> es
  | Emp -> es
  | Event _ -> es
  | Underline -> Underline
  | Cons (Cons (esIn1, esIn2), es2)-> normalES (Cons (esIn1, Cons (esIn2, es2))) 
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


  | Not (a, esARG) -> 
      let esIn = normalES  (Event (a, esARG)) in
      match esIn with
      | Event (a, b) -> Not (a, b)
      | _ -> raise (Foo "normalES NOT\n")
  ;;

let eventToEs ev : es =
  match ev with 
  | One ins -> Event ins 
  | Zero ins ->Not ins
  | Any -> Underline

  ;;


let rec string_of_event ev : string =
  match ev with 
  | One (str, ar_Li) ->  str ^ "(" ^ separate (ar_Li) (string_of_int) (",") ^")" 
  | Zero (str, ar_Li) -> "!" ^ string_of_event (One (str, ar_Li))
  | Any -> "_"

  ;;
