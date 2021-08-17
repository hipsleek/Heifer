

exception Foo of string
open Parsetree
open Asttypes
open Rewriting
open Pretty




let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;






(*
let string_of_effect_constructor x :string =
  match x.peff_kind with
  | Peff_decl(_, _) -> ""
      
  | _ -> ""
;;
type rec_flag = Nonrecursive | Recursive
*)

let string_of_payload p =
  match p with
  | PStr str -> Pprintast.string_of_structure str
  | PSig _ -> "sig"
  | PTyp _ -> "typ"
  | PPat _ -> "pattern"


let string_of_attribute (a:attribute) : string = 
  let name = a.attr_name.txt in 
  let payload = a.attr_payload in 
  Format.sprintf "name: %s, payload: %s" name (string_of_payload payload)

let string_of_attributes (a_l:attributes): string = 
  List.fold_left (fun acc a -> acc ^ string_of_attribute a ) "" a_l;;

let string_of_arg_label a = 
  match a with 
  | Nolabel -> ""
  | Labelled str -> str (*  label:T -> ... *)
  | Optional str -> "?" ^ str (* ?label:T -> ... *)

;;

let rec string_of_core_type (p:core_type) :string =
  match p.ptyp_desc with 
  | Ptyp_any -> "_"
  | Ptyp_var str -> str
  | Ptyp_arrow (a, c1, c2) -> string_of_arg_label a ^  string_of_core_type c1 ^ " -> " ^ string_of_core_type c2 ^"\n"
  | Ptyp_constr (l, c_li) -> 
    List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)^
    List.fold_left (fun acc a -> acc ^ string_of_core_type a) "" c_li
  | Ptyp_poly (str_li, c) -> 
    "type " ^ List.fold_left (fun acc a -> acc ^ a.txt) "" str_li ^ ". " ^
    string_of_core_type c 


  | _ -> "\nlsllsls\n"
  ;;


let string_of_kind k : string = 
  match k with 
  | Peff_decl (inp,outp)-> 
    List.fold_left (fun acc a -> acc ^ string_of_core_type a) "" inp 
    ^
    string_of_core_type outp
    
  | Peff_rebind _ -> "Peff_rebind"
  ;;

let string_of_p_constant con : string =
  match con with 
  | Pconst_char i -> String.make 1 i
  | Pconst_string (i, _, None) -> i
  | Pconst_string (i, _, Some delim) -> i ^ delim
  | Pconst_integer (i, None) -> i
  | _ -> "string_of_p_constant"
;;

(*

  | Pconst_integer (i, Some m) ->
  paren (first_is '-' i) (fun f (i, m) -> pp f "%s%c" i m) f (i,m)
  | Pconst_float (i, None) ->
  paren (first_is '-' i) (fun f -> pp f "%s") f i
  | Pconst_float (i, Some m) ->
  paren (first_is '-' i) (fun f (i,m) -> pp f "%s%c" i m) f (i,m)
  *)

let rec string_of_pattern (p) : string = 
  match p.ppat_desc with 
  | Ppat_any -> "_"
  (* _ *)
  | Ppat_var str -> str.txt
  (* x *)
  | Ppat_constant con -> string_of_p_constant con
  | Ppat_type l -> List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)
  | Ppat_constraint (p1, c) -> string_of_pattern p1 ^ " : "^ string_of_core_type c
  (* (P : T) *)
  | Ppat_effect (p1, p2) -> string_of_pattern p1 ^ string_of_pattern p2 ^ "\n"

  | Ppat_construct (l, None) -> List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)
  | Ppat_construct (l, Some p1) ->  
    List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt) ^ 
    string_of_pattern p1
  (* #tconst *)

  | _ -> "string_of_pattern\n" ;;


(** Given the RHS of a let binding, returns the es it is annotated with *)
let function_spec rhs =
  let attribute = false in
  if attribute then
    (* this would be used if we encode effect specs in OCaml terms via ppx *)
    (* we could do both *)
    failwith "not implemented"
  else
    let rec traverse_to_body e =
      match e.pexp_desc with
      | Pexp_fun (_, _, _, body) -> traverse_to_body body
      | _ -> e.pexp_effectspec
    in
    traverse_to_body rhs

let string_of_effectspec spec:string =
    match spec with
    | None -> "<no spec given>"
    | Some (pr, po) -> Format.sprintf "requires %s ensures %s" (string_of_spec pr) (string_of_spec po)

let string_of_value_binding vb : string = 
  let pattern = vb.pvb_pat in 
  let expression = vb.pvb_expr in
  let attributes = vb.pvb_attributes in 
  Format.sprintf "%s = %s\n%s\n%s\n"
    (string_of_pattern pattern)
    (Pprintast.string_of_expression expression)
    (string_of_attributes attributes)
    (string_of_effectspec (function_spec expression))

  ;;



let string_of_program x : string =
  (* Pprintast.string_of_structure [x] *)
  match x.pstr_desc with
  | Pstr_value (_, l) ->
    List.fold_left (fun acc a -> acc ^ string_of_value_binding a) "" l
     
  | Pstr_effect ed -> 
    let name = ed.peff_name.txt in 
    let kind = ed.peff_kind in 
    (name^ " : " ^ string_of_kind kind)
  | _ ->  ("empty")


let debug_string_of_expression e =
  Format.asprintf "%a" (Printast.expression 0) e

(*
let getIndentName (l:Longident.t loc): string = 
  (match l.txt with 
        | Lident str -> str
        | _ -> "dont know"
        )
        ;;

let rec findValue_binding name vbs: (specification * specification) option = 
  match vbs with 
  | [] -> None 
  | vb :: xs -> 
    let pattern = vb.pvb_pat in 
    let expression = vb.pvb_expr in 
    if String.compare (string_of_pattern pattern) name == 0 then 
    
    (match function_spec expression with 
      | None -> Some ((Emp, []), (Emp, []))
      | Some (pre, post) -> Some (normalSpec pre, normalSpec post)
    )
   else findValue_binding name xs ;;


  (*  
  Some (Emp, Cons (Event(One ("Foo", [])), Event(One ("Foo", []))))

  let expression = vb.pvb_expr in
  let attributes = vb.pvb_attributes in 

  string_of_expression expression ^  "\n" ^
  string_of_attributes attributes ^ "\n"
  *)
  ;;

        
let is_stdlib_fn name =
  match name with
  | "!" -> true
  | _ -> false

let rec findProg name full: (specification * specification) = 
  match full with 
  | [] when is_stdlib_fn name -> ((Emp, []), (Emp, []))
  | [] -> raise (Foo ("findProg: function " ^ name ^ " is not found!"))
  | x::xs -> 
    match x.pstr_desc with
    | Pstr_value (_ (*rec_flag*), l (*value_binding list*)) ->
        (match findValue_binding name l with 
        | Some (pre, post) -> (pre, post)
        | None -> findProg name xs
        )
    | _ ->  findProg name xs
  ;;

;;

let call_function fnName (li:(arg_label * expression) list) acc progs : specification = 

  let name = 
    match fnName.pexp_desc with 
    | Pexp_ident l -> getIndentName l 
        
    | _ -> "dont know"

  in 

  
  if String.compare name "perform" == 0 then 
    let (_, temp) = (List.hd li) in 
    let eff_l = match temp.pexp_desc with 
      | Pexp_construct (a, _) -> Event (getIndentName a)
      | _ -> Emp
    in 
    Cons (acc, eff_l)
  else if String.compare name "continue" == 0 then 
    acc
  else 
    let ((* param_formal, *) precon, postcon) = findProg name progs in 
    let (res, _) = check_containment acc precon in 
    if res then Cons (acc, postcon)
    else raise (Foo ("call_function precondition fail:" ^ debug_string_of_expression fnName));;


let checkRepeat history fst : (event list) option = 

  let rev_his = List.rev history in 
  let rec aux acc li = 
    match li with 
    | [] -> None 
    | x::xs -> 
      if compareEvent x fst then Some (acc)
      else aux (x::acc) xs 
  in aux [fst] rev_his ;;

let rec eventListToES history : es =
  match history with 
  | [] -> Emp
  | x::xs -> Cons (eventToEs x, eventListToES xs )
  ;;


let fixpoint es policy: es =
  let es = normalES es in 
  let policy = List.map (fun (a, b) -> (a, normalES b)) policy in 
  let fst_list = (fst es) in 

  let rec innerAux history fst:es =   
    match checkRepeat history fst with 
    | None -> 
    let rec helper p = 
      match p with
      | [] -> raise (Foo ("fixpoint: Effect" ^ string_of_es (eventToEs fst) ^ " is not catched"))
      | (x, trace)::xs -> 
        if compareEvent x fst then 
          let new_start = (esTail trace) in 
          Cons (trace, 
          if List.length (new_start) == 0 then Emp
          else 
          List.fold_left (fun acc f -> ESOr (acc, innerAux (List.append history [fst]) f)) Bot  new_start
          )
         else helper xs 
        
    in helper policy
    | Some ev_li -> 
      Omega (eventListToES ev_li)

  in 

  List.fold_left (fun accFst f -> 
  let der = derivative es f in 


  let rec aux fst der acc: es = 
    let cur = Cons (eventToEs fst, innerAux [] fst) in 
    if isEmp der then Cons (acc, cur)
    else 
      let new_ev = List.hd (Rewriting.fst es) in 
      let new_der = derivative der new_ev in 

      aux new_ev new_der (Cons (acc, cur))
    
  in ESOr (accFst, aux f der Emp)
  ) Bot fst_list
  ;;





        (*print_string (List.fold_left (fun acc (l, r) -> acc ^
          (match l with 
          | None -> "none "
          | Some  str -> str
         ) ^ " -> " ^ string_of_es r ^"\n"
          ) "" policy);
                  raise (Foo ("rangwo chou chou: "^ string_of_es es1));
          *)
        


let rec getNormal p: es = 
  match p with  
  | [] -> raise (Foo "getNormal: there is no handlers for normal return")
  | (None, es)::_ -> es
  | _ :: xs -> getNormal xs
  ;;


let rec getHandlers p: (event * es) list = 
  match p with  
  | [] -> []
  | (None, _)::xs -> getHandlers xs 
  | (Some str, es) :: xs -> ( (One str), es) :: getHandlers xs
  ;;



let rec infer_of_expression progs acc expr : es =
  match expr.pexp_desc with 
  | Pexp_fun (_, _, _ (*pattern*), expr) -> infer_of_expression progs acc expr 
  | Pexp_apply (fnName, li) (*expression * (arg_label * expression) list*)
    -> 

    let temp = List.map (fun (_, a) -> a) li in 
    let arg_eff = List.fold_left (fun acc a -> Cons(acc, infer_of_expression progs acc a)) Emp temp in 
    call_function fnName li (Cons(acc, arg_eff)) progs
  | Pexp_construct _ ->  Emp
  | Pexp_constraint (ex, _) -> infer_of_expression progs acc ex
  | Pexp_sequence (ex1, ex2) -> 

    let acc1 = infer_of_expression progs acc ex1 in 

    infer_of_expression progs acc1 ex2

  | Pexp_match (ex, case_li) -> 
    let es1 = infer_of_expression progs Emp ex in 
    let policy = List.map (fun a -> 
      let lhs = a.pc_lhs in 
      let rhs = a.pc_rhs in 
      
      let temp = match lhs.ppat_desc with 
        | Ppat_effect (p1, _) ->  Some (string_of_pattern p1)
        | _ -> None 
      in 
      (
        temp,
        infer_of_expression progs Emp rhs
      )) case_li in 

      if isEmp (normalES es1) then getNormal policy 
      else fixpoint es1 (getHandlers policy)
    
    
  | Pexp_ident _
  | Pexp_constant _ -> Emp

  | Pexp_let (_rec, _bindings, c) -> 
    (* TODO do bindings *)
    infer_of_expression progs acc c
  | Pexp_try (body, _cases) -> 
    (* TODO do cases *)
    infer_of_expression progs acc body

  | _ -> raise (Foo ("infer_of_expression: " ^ debug_string_of_expression expr))

  

let infer_of_value_binding progs vb: string = 
  let pattern = vb.pvb_pat in 
  let expression = vb.pvb_expr in
  let spec = 
    match function_spec expression with 
    | None -> (Emp, Emp)
    | Some (pre, post) -> (normalES pre, normalES post)
  in 
  let (pre, post) = spec in (* postcondition *)
  let final = normalES (infer_of_expression progs pre expression) in 

    "\n========== Module: "^ string_of_pattern pattern ^" ==========\n" ^
    "[Pre  Condition] " ^ string_of_es pre ^"\n"^
    "[Post Condition] " ^ string_of_es post ^"\n"^
    "[Final  Effects] " ^ string_of_es final ^"\n\n"^
    (*(string_of_inclusion final_effects post) ^ "\n" ^*)
    "[T.r.s: Verification for Post Condition]\n" ^ 
    printReport final post

    ;;


  (*

  let attributes = vb.pvb_attributes in 
  string_of_attributes attributes ^ "\n"
  *)


  

let infer_of_program progs x:  string =
  match x.pstr_desc with
  | Pstr_value (_ (*rec_flag*), x::_ (*value_binding list*)) ->
    infer_of_value_binding progs x 
    
  | Pstr_effect _ -> string_of_es Emp
  | _ ->  string_of_es Bot
  ;;
  *)

let debug_tokens str =
  let lb = Lexing.from_string str in
  let rec loop tokens =
    let tok = Lexer.token lb in
    match tok with
    | EOF -> List.rev (tok :: tokens)
    | _ -> loop (tok :: tokens)
  in
  let tokens = loop [] in
  let s = tokens |> List.map Debug.string_of_token |> String.concat " " in
  Format.printf "%s@." s



let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      
      (* debug_tokens line; *)

      let progs = Parser.implementation Lexer.token (Lexing.from_string line) in

      
      (* Dump AST -dparsetree-style *)
      (* Format.printf "%a@." Printast.implementation progs; *)

      (*print_string (Pprintast.string_of_structure progs ) ; *)
      print_endline (List.fold_left (fun acc a -> acc ^ "\n" ^ string_of_program a) "" progs);

      print_endline (testSleek ());
      (* 
      print_endline (List.fold_left (fun acc a -> acc ^ (infer_of_program progs a) ^ "\n" ) "\n" progs);

      *)
      (*print_endline (Pprintast.string_of_structure progs ) ; 
      print_endline ("---");
      print_endline (List.fold_left (fun acc a -> acc ^ forward a) "" progs);*)
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with
    | Pretty.Foo s ->
      print_endline "\nINTERNAL ERROR:\n";
      print_endline s
    | e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;

