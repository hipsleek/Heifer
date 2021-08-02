

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

let string_of_effectspec spec =
    match spec with
    | None -> "<no spec given>"
    | Some (pr, po) -> Format.sprintf "requires %s ensures %s" (string_of_es pr) (string_of_es po)

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



let string_of_program x : string= 
  match x.pstr_desc with
  | Pstr_value (_, l) ->
    List.fold_left (fun acc a -> acc ^ string_of_value_binding a) "" l
     
  | Pstr_effect ed -> 
    let name = ed.peff_name.txt in 
    let kind = ed.peff_kind in 
    (name^ " : " ^ string_of_kind kind)
  | _ ->  ("empty")
  ;;




let string_of_expression_desc desc: string = 
  match desc with 
  | Pexp_ident _ -> "Pexp_ident"
        (* x
           M.x
         *)
  | Pexp_constant _ -> "Pexp_constant"
        (* 1, 'a', "true", 1.0, 1l, 1L, 1n *)
  | Pexp_let _ -> "Pexp_let"
        (* let P1 = E1 and ... and Pn = EN in E       (flag = Nonrecursive)
           let rec P1 = E1 and ... and Pn = EN in E   (flag = Recursive)
         *)
  | Pexp_function _ -> "Pexp_function"
        (* function P1 -> E1 | ... | Pn -> En *)
  | Pexp_fun _ -> "Pexp_fun"
        (* fun P -> E1                          (Simple, None)
           fun ~l:P -> E1                       (Labelled l, None)
           fun ?l:P -> E1                       (Optional l, None)
           fun ?l:(P = E0) -> E1                (Optional l, Some E0)

           Notes:
           - If E0 is provided, only Optional is allowed.
           - "fun P1 P2 .. Pn -> E1" is represented as nested Pexp_fun.
           - "let f P = E" is represented using Pexp_fun.
         *)
  | Pexp_apply _ -> "Pexp_apply"
        (* E0 ~l1:E1 ... ~ln:En
           li can be empty (non labeled argument) or start with '?'
           (optional argument).

           Invariant: n > 0
         *)
  | Pexp_match _ -> "Pexp_match"
        (* match E0 with P1 -> E1 | ... | Pn -> En *)
  | Pexp_try _ -> "Pexp_try"
        (* try E0 with P1 -> E1 | ... | Pn -> En *)
  | Pexp_tuple _ -> "Pexp_tuple"
        (* (E1, ..., En)

           Invariant: n >= 2
        *)
  | Pexp_construct _ -> "Pexp_construct"
        (* C                None
           C E              Some E
           C (E1, ..., En)  Some (Pexp_tuple[E1;...;En])
        *)
  | Pexp_variant _ -> "Pexp_variant"
        (* `A             (None)
           `A E           (Some E)
         *)
  | Pexp_record _ -> "Pexp_record"
        (* { l1=P1; ...; ln=Pn }     (None)
           { E0 with l1=P1; ...; ln=Pn }   (Some E0)

           Invariant: n > 0
         *)
  | Pexp_field _ -> "Pexp_field"
        (* E.l *)
  | Pexp_setfield _ -> "Pexp_setfield"
        (* E1.l <- E2 *)
  | Pexp_array _ -> "Pexp_array"
        (* [| E1; ...; En |] *)
  | Pexp_ifthenelse _ -> "Pexp_ifthenelse"
        (* if E1 then E2 else E3 *)
  | Pexp_sequence _ -> "Pexp_sequence"
        (* E1; E2 *)
  | Pexp_while _ -> "Pexp_while"
        (* while E1 do E2 done *)
  | Pexp_for _ -> "Pexp_for"
        (* for i = E1 to E2 do E3 done      (flag = Upto)
           for i = E1 downto E2 do E3 done  (flag = Downto)
         *)
  | Pexp_constraint _ -> "Pexp_constraint"
        (* (E : T) *)
  | Pexp_coerce _ -> "Pexp_coerce"
        (* (E :> T)        (None, T)
           (E : T0 :> T)   (Some T0, T)
         *)
  | Pexp_send _ -> "Pexp_send"
        (*  E # m *)
  | Pexp_new _ -> "Pexp_new"
        (* new M.c *)
  | Pexp_setinstvar _ -> "Pexp_setinstvar"
        (* x <- 2 *)
  | Pexp_override _ -> "Pexp_override"
        (* {< x1 = E1; ...; Xn = En >} *)
  | Pexp_letmodule _ -> "Pexp_letmodule"
        (* let module M = ME in E *)
  | Pexp_letexception _ -> "Pexp_letexception"
        (* let exception C in E *)
  | Pexp_assert _ -> "Pexp_assert"
        (* assert E
           Note: "assert false" is treated in a special way by the
           type-checker. *)
  | Pexp_lazy _ -> "Pexp_lazy"
        (* lazy E *)
  | Pexp_poly _ -> "Pexp_poly"
        (* Used for method bodies.

           Can only be used as the expression under Cfk_concrete
           for methods (not values). *)
  | Pexp_object _ -> "Pexp_object"
        (* object ... end *)
  | Pexp_newtype _ -> "Pexp_newtype"
        (* fun (type t) -> E *)
  | Pexp_pack _ -> "Pexp_pack"
        (* (module ME)

           (module ME : S) is represented as
           Pexp_constraint(Pexp_pack, Ptyp_package S) *)
  | Pexp_open _ -> "Pexp_open"
        (* M.(E)
           let open M in E
           let! open M in E *)
  | Pexp_letop _ -> "Pexp_letop"
        (* let* P = E in E
           let* P = E and* P = E in E *)
  | Pexp_extension _ -> "Pexp_extension"
        (* [%id] *)
  | Pexp_unreachable  -> "Pexp_unreachable"
        (* . *)



let getIndentName (l:Longident.t loc): string = 
  (match l.txt with 
        | Lident str -> str
        | _ -> "dont know"
        )
        ;;

let rec findValue_binding name vbs: (es * es) option = 
  match vbs with 
  | [] -> None 
  | vb :: xs -> 
    let pattern = vb.pvb_pat in 
    let expression = vb.pvb_expr in 
    if String.compare (string_of_pattern pattern) name == 0 then 
    
    (match function_spec expression with 
      | None -> Some (Emp, Emp)
      | Some (pre, post) -> Some (normalES pre, normalES post)
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

        

let rec findProg name full: (es * es) = 
  match full with 
  | [] -> raise (Foo ("function " ^ name ^ " is not found!"))
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

let call_function fnName (li:(arg_label * expression) list) acc progs : es = 

  let name = 
    match fnName.pexp_desc with 
    | Pexp_ident l -> getIndentName l 
        
    | _ -> "dont know"

  in 

  
  if String.compare name "perform" == 0 then 
    let (_, temp) = (List.hd li) in 
    let eff_l = match temp.pexp_desc with 
      | Pexp_construct (a, _) -> Event (getIndentName a, [])
      | _ -> Emp
    in 
    Cons (acc, eff_l)
  else if String.compare name "continue" == 0 then 
    acc
  else 
    let ((* param_formal, *) precon, postcon) = findProg name progs in 
    let (res, _) = check_containment acc precon in 
    if res then Cons (acc, postcon)
    else raise (Foo ("Call_function precondition fail:" ^ string_of_expression_desc (fnName.pexp_desc)));;


let checkRepeat history fst : (event list) option = 
  print_string ("checkRepeat: "^ List.fold_left (fun acc a -> acc ^ string_of_event a ) "" history);

  let rev_his = List.rev history in 
  let rec aux acc li = 
    match li with 
    | [] -> None 
    | x::xs -> 
      if compareEvent x fst then Some (List.rev (List.append acc [x]))
      else aux (List.append acc [x]) xs 
  in aux [] rev_his ;;

let rec eventListToES history : es =
  match history with 
  | [] -> Emp
  | x::xs -> Cons (eventToEs x, eventListToES xs )
  ;;


let fixpoint es policy: es =
  let es = normalES es in 
  let policy = List.map (fun (a, b) -> (a, normalES b)) policy in 
  let ev = List.hd (fst es) in 
  let der = derivative es ev in 


  let rec innerAux history fst:es =   
    match checkRepeat history fst with 
    | None -> 
    let rec helper p = 
      match p with
      | [] -> raise (Foo ("Effect" ^ string_of_es (eventToEs fst) ^ " is not catched"))
      | (x, trace)::xs -> 
        if compareEvent x fst then 
          let new_start = List.hd (esTail trace) in 
          Cons (trace, 
          innerAux (List.append history [fst])  new_start
          )
         else helper xs 
        
    in helper policy
    | Some ev_li -> 
      Omega (eventListToES ev_li)

  in 

  let rec aux fst der acc: es = 
    let cur = Cons (eventToEs fst, innerAux [] fst) in 
    if isEmp der then Cons (acc, cur)
    else 
      let new_ev = List.hd (Rewriting.fst es) in 
      let new_der = derivative der new_ev in 

      aux new_ev new_der (Cons (acc, cur))
    
  in aux ev der Emp ;;





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
  | [] -> raise (Foo "there is no handlers for normal return")
  | (None, es)::_ -> es
  | _ :: xs -> getNormal xs
  ;;


let rec getHandlers p: (event * es) list = 
  match p with  
  | [] -> []
  | (None, _)::xs -> getHandlers xs 
  | (Some str, es) :: xs -> ( (One ((str, []))), es) :: getHandlers xs
  ;;



let rec infer_of_expression progs acc expr : es =
  let infer_of_expression_desc desc : es =
    match desc with 
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
      
      
    | Pexp_ident _ -> Emp

    | _ -> raise (Foo ("infer_of_expression_desc: " ^ string_of_expression_desc desc))
  in 
  let desc = expr.pexp_desc in 
  infer_of_expression_desc desc ;;

  

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
      print_string (List.fold_left (fun acc a -> acc ^ string_of_program a) "" progs);

      print_string (List.fold_left (fun acc a -> acc ^ (infer_of_program progs a) ^ "\n" ) "\n" progs);

      (*print_endline (Pprintast.string_of_structure progs ) ; 
      print_endline ("---");
      print_endline (List.fold_left (fun acc a -> acc ^ forward a) "" progs);*)
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;

