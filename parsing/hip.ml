

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

let collect_param_names rhs =
  let rec traverse_to_body e =
    match e.pexp_desc with
    | Pexp_fun (_, _, name, body) ->
      let name =
        match name.ppat_desc with
        | Ppat_var s -> [s.txt]
        | _ ->
          (* we don't currently recurse inside patterns to pull out variables, so something like

             let f () (Foo a) = 1

             will be treated as if it has no formal params. *)
          []
      in
      name @ traverse_to_body body
    | _ -> []
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

let merge_spec (p1, es1, side1) (p2, es2, side2) : spec = 
  (And (p1, p2), Cons(es1, es2), List.append side1 side2);;


let getIndentName (l:Longident.t loc): string = 
  (match l.txt with 
        | Lident str -> str
        | _ -> "dont know"
        )
        ;;

module SMap = Map.Make (struct
  type t = string
  let compare = compare
end)

(* information we record after seeing a function *)
type fn_spec = {
  pre: spec;
  post: spec;
  formals: string list;
}

(* at a given program point, this captures specs for all local bindings *)
type fn_specs = fn_spec SMap.t

type env = {
  (* module name -> a bunch of function specs *)
  modules : fn_specs SMap.t;
  current : fn_specs
}

module Env = struct
  let empty = { modules = SMap.empty; current = SMap.empty }

  let add_fn f spec env =
    { env with current = SMap.add f spec env.current }

  let find_fn f env =
    SMap.find f env.current

  let add_module name menv env =
    { env with modules = SMap.add name menv.current env.modules }

  (* dump all the bindings for a given module into the current environment *)
  let open_module name env =
    let m = SMap.find name env.modules in
    let fns = SMap.bindings m |> List.to_seq in
    { env with current = SMap.add_seq fns env.current }
end

let string_of_fn_specs specs =
  Format.sprintf "{%s}"
    (SMap.bindings specs
    |> List.map (fun (n, s) ->
      Format.sprintf "%s -> %s/%s/%s" n
        (string_of_spec s.pre)
        (string_of_spec s.post)
        (s.formals |> String.concat ","))
    |> String.concat "; ")

let string_of_env env =
  Format.sprintf "%s\n%s"
    (env.current |> string_of_fn_specs)
    (env.modules
      |> SMap.bindings
      |> List.map (fun (n, s) -> Format.sprintf "%s: %s" n (string_of_fn_specs s))
      |> String.concat "\n")

let rec findValue_binding name vbs: (string list) option =
  match vbs with 
  | [] -> None 
  | vb :: xs -> 
    let pattern = vb.pvb_pat in 
    let expression = vb.pvb_expr in 

    let rec helper ex= 
      match ex.pexp_desc with 
      | Pexp_fun (_, _, p, exIn) -> (string_of_pattern p) :: (helper exIn)
      | _ -> []
    in

    let arg_formal = helper expression in 
    
  
    if String.compare (string_of_pattern pattern) name == 0 then Some arg_formal
    
    (*match function_spec expression with 
      | None -> 
      | Some (pre, post) -> Some {pre = normalSpec pre; post = normalSpec post; formals = []}
    *)
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

let rec find_arg_formal name full: string list = 
  match full with 
  | [] when is_stdlib_fn name -> []
  | [] -> raise (Foo ("findProg: function " ^ name ^ " is not found!"))
  | x::xs -> 
    match x.pstr_desc with
    | Pstr_value (_ (*rec_flag*), l (*value_binding list*)) ->
        (match findValue_binding name l with 
        | Some spec -> spec
        | None -> find_arg_formal name xs
        )
    | _ ->  find_arg_formal name xs
  ;;

;;

let rec side_binding (formal:string list) (actual: spec list) : side = 
  match (formal, actual) with 
  | (x::xs, (_, y, _)::ys) -> (x, y) :: (side_binding xs ys)
  | _ -> []
  ;;



let call_function fnName (li:(arg_label * expression) list) (acc:spec) (arg_eff:spec list) env : spec = 
  let (acc_pi, acc_es, acc_side) = acc in 
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
    (acc_pi, Cons (acc_es, eff_l), acc_side)
  else if String.compare name "continue" == 0 then 
    acc
  else 
    let (* param_formal, *) 
    { pre = precon ; post = (post_pi, post_es, post_side); formals = arg_formal } = Env.find_fn name env in
    let sb = side_binding (*find_arg_formal name env*) arg_formal arg_eff in 
    let (res, str) = printReport (merge_spec acc (True, Emp, sb)) precon in 
    if res then (And(acc_pi, post_pi), Cons (acc_es, post_es), List.append acc_side post_side)
    else raise (Foo ("call_function precondition fail:" ^ str ^ debug_string_of_expression fnName));;


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

(*
let fixpoint ((_, es, _):spec) (policy: (string option * spec) list): spec =
  let es = normalES es in 
  let policy = List.map (fun (a, b) -> (a, normalSpec b)) policy in 
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
        
*)

let rec getNormal (p: (string option * spec) list): spec = 
  match p with  
  | [] -> raise (Foo "getNormal: there is no handlers for normal return")
  | (None, s)::_ -> s
  | _ :: xs -> getNormal xs
  ;;


let rec getHandlers p: (event * es) list = 
  match p with  
  | [] -> []
  | (None, _)::xs -> getHandlers xs 
  | (Some str, es) :: xs -> ( (One str), es) :: getHandlers xs
  ;;




let rec infer_of_expression env (acc:spec) expr : spec =

  match expr.pexp_desc with 
  | Pexp_fun (_, _, _ (*pattern*), expr) -> infer_of_expression env acc expr 
  | Pexp_apply (fnName, li) (*expression * (arg_label * expression) list*)
    -> 
    let temp = List.map (fun (_, a) -> a) li in 
    let arg_eff = List.fold_left 
    (fun acc_li a -> 
      let a_spec = infer_of_expression env (True, Emp, []) a in 
      
      List.append acc_li [a_spec]
      ) 
    [] temp in 


    call_function fnName li acc arg_eff env
  | Pexp_construct _ -> (True, Emp, [])
  | Pexp_constraint (ex, _) -> infer_of_expression env acc ex
  | Pexp_sequence (ex1, ex2) -> 

    let acc1 = infer_of_expression env acc ex1 in 

    infer_of_expression env acc1 ex2

  | Pexp_match (ex, case_li) -> 
    let es1 = infer_of_expression env (True, Emp, []) ex in 
    let policy = List.map (fun a -> 
      let lhs = a.pc_lhs in 
      let rhs = a.pc_rhs in 
      
      let temp = match lhs.ppat_desc with 
        | Ppat_effect (p1, _) ->  Some (string_of_pattern p1)
        | _ -> None 
      in 
      (
        temp,
        infer_of_expression env (True, Emp, []) rhs
      )) case_li in 

      if isEmpSpec (normalSpec es1) then getNormal policy 
      
      else raise (Foo "fixpoint es1 (getHandlers policy)")
    
    
  | Pexp_ident _
  | Pexp_constant _ -> (True, Emp, [])

  | Pexp_let (_rec, bindings, c) -> 

    let env =
      List.fold_left (fun env vb ->
        let _, _, _, env, _ = infer_value_binding env vb in env) env bindings
    in

    infer_of_expression env acc c
  | Pexp_try (body, _cases) -> 
    (* TODO do cases *)
    infer_of_expression env acc body

  | _ -> raise (Foo ("infer_of_expression: " ^ debug_string_of_expression expr))

  
and infer_value_binding env vb = 
  let fn_name = string_of_pattern vb.pvb_pat in
  let body = vb.pvb_expr in
  let formals = collect_param_names body in
  let spec = 
    match function_spec body with
    | None -> ((True, Emp, []), (True, Emp, []))
    | Some (pre, post) -> (normalSpec pre, normalSpec post)
  in 
  let (pre, post) = spec in
  let (pre_p, pre_es, _) = pre in 
  let final = normalSpec (infer_of_expression env (pre_p, pre_es, []) body) in
  let env1 = Env.add_fn fn_name { pre; post; formals } env in
  pre, post, final, env1, fn_name


let infer_of_value_binding env vb: string * env = 
  let pre, post, final, env, fn_name = infer_value_binding env vb in

    "\n========== Function: "^ fn_name ^" ==========\n" ^
    "[Pre  Condition] " ^ string_of_spec pre ^"\n"^
    "[Post Condition] " ^ string_of_spec post ^"\n"^
    "[Final  Effects] " ^ string_of_spec final ^"\n\n"^
    (*(string_of_inclusion final_effects post) ^ "\n" ^*)
    (*"[T.r.s: Verification for Post Condition]\n" ^ *)
    (let (_, str) = printReport final post in str), env

    ;;


  (*

  let attributes = vb.pvb_attributes in 
  string_of_attributes attributes ^ "\n"
  *)


  

let rec infer_of_program env x: string * env =
  match x.pstr_desc with
  | Pstr_value (_ (*rec_flag*), x::_ (*value_binding list*)) ->
    infer_of_value_binding env x 
    
  | Pstr_module m ->
    (* when we see a module, infer inside it *)
    let name = m.pmb_name.txt |> Option.get in
    let res, menv =
      match m.pmb_expr.pmod_desc with
      | Pmod_structure str ->
        List.fold_left (fun (s, env) si ->
          let r, env = infer_of_program env si in
          r :: s, env) ([], env) str
      | _ -> failwith "infer_of_program: unimplemented module expression type"
    in
    let res = String.concat "\n" (Format.sprintf "--- Module %s---" name :: res) in
    let env1 = Env.add_module name menv env in
    res, env1

  | Pstr_open info ->
    (* when we see a structure item like: open A... *)
    let name =
      match info.popen_expr.pmod_desc with
      | Pmod_ident name ->
      begin match name.txt with
      | Lident s -> s
      | _ -> failwith "infer_of_program: unimplemented open type, can only open names"
      end
      | _ -> failwith "infer_of_program: unimplemented open type, can only open names"
    in
    (* ... dump all the bindings in that module into the current environment and continue *)
    "", Env.open_module name env

  | Pstr_effect _ -> string_of_es Emp, env
  | _ ->  string_of_es Bot, env
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
      print_endline (List.fold_left (fun acc a -> acc ^ "\n" ^ string_of_program a) "" progs);

      let results, _ =
        List.fold_left (fun (s, env) a ->
          let spec, env1 = infer_of_program env a in
          spec :: s, env1
        ) ([], Env.empty) progs
      in
      print_endline (results |> List.rev |> String.concat "\n");

      (* 
      print_endline (testSleek ());

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

