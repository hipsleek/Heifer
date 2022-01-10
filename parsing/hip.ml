

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

let debug_string_of_core_type t =
  Format.asprintf "type %a@." Pprintast.core_type t

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

  
  | _ -> Format.asprintf "string_of_pattern: %a\n" Pprintast.pattern p;;


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

let string_of_longident l =
  l |> Longident.flatten |> String.concat "."

let merge_spec (p1, es1, side1) (p2, es2, side2) : spec = 
  (And (p1, p2), Cons(es1, es2), List.append side1 side2);;


let getIndentName (l:Longident.t loc): string = 
  (match l.txt with 
        | Lident str -> str
        | _ -> "getIndentName: dont know " ^ string_of_longident l.txt
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

(* only first-order types for arguments, for now *)
type typ = TInt | TUnit | TRef of typ

let rec core_type_to_typ (t:core_type) =
  match t.ptyp_desc with
  | Ptyp_constr ({txt=Lident "int"; _}, []) -> TInt
  | Ptyp_constr ({txt=Lident "unit"; _}, []) -> TUnit
  | Ptyp_constr ({txt=Lident "ref"; _}, [t]) -> TRef (core_type_to_typ t)
  | _ -> failwith ("core_type_to_typ: " ^ string_of_core_type t)

(* effect Foo : int -> (int -> int) *)
type effect_def = {
  params: typ list; (* [TInt] *)
  res: typ list * typ (* ([TInt], TInt) *)
}

type env = {
  (* module name -> a bunch of function specs *)
  modules : fn_specs SMap.t;
  current : fn_specs;
  (* the stack stores higher-order functions which may produce effects.
     an entry like a -> Foo(1) means that the variable a in scope has been applied to
     the single argument 1. nothing is said about how many arguments are remaining,
     (though that can be figured out from effect_defs) *)
  stack : stack list;
  (* remembers types given in effect definitions *)
  side_spec : side;
  effect_defs : effect_def SMap.t;
}

module Env = struct
  let empty = {
    modules = SMap.empty;
    current = SMap.empty;
    stack = [];
    side_spec = [];
    effect_defs = SMap.empty
  }

  let add_fn f spec env =
    { env with current = SMap.add f spec env.current }

  let add_side_spec side_list env =
    { env with side_spec = List.append (env.side_spec) side_list }

  let reset_side_spec side_list env =
    { env with side_spec = side_list }

  let add_stack paris env = 
    { env with stack = List.append  paris (env.stack) }

  let add_effect name def env =
    { env with effect_defs = SMap.add name def env.effect_defs }

  let find_fn f env =
    SMap.find_opt f env.current
  
  let fine_side f env = 
    let rec aux e =
      match e with 
      | [] -> None
      | (s, (_pre, _post)) :: xs -> 
        if String.compare s f ==0 
        then 
          let __pre = (True, _pre, []) in 
          let __post = (True, _post, []) in 
          Some (__pre, __post) else aux xs
    in aux env.side_spec
  
  let find_effect_arg_length name env =
    match SMap.find_opt name env.effect_defs with 
    | None -> None 
    | Some def -> 
      let n1 = List.length (def.params)  in 
      let (a, _) = def.res in 
      let n2 = List.length a in 
      Some (n1 + n2)


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

let rec eliminatePartial (es:es) env :es = 
  match es with

  | Predicate (eff_name, arg_list) ->
    let eff_arg_length = List.length  arg_list in 
    let eff_formal_arg_length = Env.find_effect_arg_length eff_name env in 
    (match eff_formal_arg_length with 
    | None -> raise (Foo (eff_name ^ " is not defined"))
    | Some n -> 
      (*if String.compare eff_name "Goo" == 0 then 
      raise (Foo (string_of_int eff_arg_length ^ ":"^ string_of_int n))
      else 
      *)
      (*4 Q when it is at the end, no need to add Q *)
      if eff_arg_length < n || eff_arg_length == 0 then Emp else es 
    )


  | Cons (es1, es2) ->  Cons (eliminatePartial es1 env, eliminatePartial es2 env)
      
  | ESOr (es1, es2) -> ESOr (eliminatePartial es1 env, eliminatePartial es2 env)
      
  | Omega es1 -> Omega (eliminatePartial es1 env)
      
  | Kleene es1 -> Kleene (eliminatePartial es1 env)

  | Bot -> es
  | Emp -> es
  | Event _ -> es
  | Not _ -> es 
  | Underline -> es
      



  ;;

let eliminatePartiaShall spec env : spec = 
  let (pi, es, side) = spec in 
  (pi, eliminatePartial es env, side);;

let rec side_binding (formal:string list) (actual: (es * es) list) : side = 
  match (formal, actual) with 
  | (x::xs, tuple::ys) -> (x, tuple) :: (side_binding xs ys)
  | _ -> []
  ;;

let fnNameToString fnName: string = 
  match fnName.pexp_desc with 
    | Pexp_ident l -> getIndentName l 
        
    | _ -> "fnNameToString: dont know " ^ debug_string_of_expression fnName
    ;;

let expressionToBasicT ex : basic_t =
  match ex.pexp_desc with 
  | Pexp_constant cons ->
    (match cons with 
    | Pconst_integer (str, _) -> BINT (int_of_string str)
    | _ -> raise (Foo (Pprintast.string_of_expression  ex ^ " expressionToBasicT error1"))
    )
  | Pexp_construct _ -> UNIT
  | Pexp_ident _ -> raise (Foo "Pexp_i")
  | Pexp_let _ -> raise (Foo "Pexp_i")
  | Pexp_function _ -> raise (Foo "Pexp_i")
  | Pexp_fun _ -> raise (Foo "Pexp_i")
  | Pexp_apply _ -> raise (Foo "Pexp_i")
  | Pexp_match _ -> raise (Foo "Pexp_iden")
  | Pexp_try _ -> raise (Foo "Pexp_iden")
  | Pexp_tuple _ -> raise (Foo "Pexp_iden")

  | Pexp_variant _ -> raise (Foo "Pexp_ident")
  | Pexp_record _ -> raise (Foo "Pexp_ident")
  | Pexp_field _ -> raise (Foo "Pexp_ident")
  | Pexp_setfield _ -> raise (Foo "Pexp_ident")
  | Pexp_array _ -> raise (Foo "Pexp_ident")
  | Pexp_ifthenelse _ -> raise (Foo "Pexp_ident")
  | Pexp_sequence _ -> raise (Foo "Pexp_ident")
  | Pexp_while _ -> raise (Foo "Pexp_ident")
  | Pexp_for _ -> raise (Foo "Pexp_ident")
  | Pexp_constraint _ -> raise (Foo "Pexp_ident")
  | Pexp_coerce _ -> raise (Foo "Pexp_ident")


  | Pexp_send _ -> raise (Foo "Pexp_ident2")
  | Pexp_new _ -> raise (Foo "Pexp_ident2")
  | Pexp_setinstvar _ -> raise (Foo "Pexp_ident2")
  | Pexp_override _ -> raise (Foo "Pexp_ident2")
  | Pexp_letmodule _ -> raise (Foo "Pexp_ident2")
  | Pexp_letexception _ -> raise (Foo "Pexp_ident2")
  | Pexp_assert _ -> raise (Foo "Pexp_ident2")
  | Pexp_lazy _ -> raise (Foo "Pexp_ident2")
  | Pexp_poly _ -> raise (Foo "Pexp_ident3")
  | Pexp_object _ -> raise (Foo "Pexp_ident3")
  | Pexp_newtype _ -> raise (Foo "Pexp_ident3")
  | Pexp_pack _ -> raise (Foo "Pexp_ident3")
  | Pexp_open _ -> raise (Foo "Pexp_ident3")
  | Pexp_letop _ -> raise (Foo "Pexp_ident3")
  | Pexp_extension _ -> raise (Foo "Pexp_ident3")
  | Pexp_unreachable  -> raise (Foo "Pexp_ident3")
 
 (* | _ -> raise (Foo (Pprintast.string_of_expression  ex ^ " expressionToBasicT error2"))
*)


let call_function (pre_es:es) fnName (li:(arg_label * expression) list) (acc:spec) (arg_eff:(es * es) list) env : (spec * residue) = 
  let (acc_pi, acc_es, acc_side) = acc in 
  let name = fnNameToString fnName in 
  let spec, residue =
    if String.compare name "perform" == 0 then 
      let getEffName l = 
        let (_, temp) = l in 
        match temp.pexp_desc with 
        | Pexp_construct (a, _) -> getIndentName a 
        | _ -> raise (Foo "getEffName error")
      in 

      let eff_name = getEffName (List.hd li) in 
      
      
      let eff_args = List.tl li in
      let iinnss = (eff_name,
      List.map (fun (_, a) -> expressionToBasicT a) eff_args) in 
      let spec = acc_pi, Cons (acc_es, Cons (Event (eff_name), Predicate iinnss)), acc_side in
      (* given perform Foo 1, residue is Some (Foo, [BINT 1]) *)
      let residue = Some iinnss in

      (spec, residue)
    else if String.compare name "continue" == 0 then 

      let (policy:spec) = List.fold_left (
        fun (acc_pi, acc_es, acc_side) (_, a_post) -> 
          (acc_pi, Cons(acc_es, a_post), acc_side)) acc arg_eff in 
      (policy, None)
      (*
      (acc, None)
      *)
    else if List.mem_assoc name env.stack then
      (* higher-order function, so we should produce some residue instead *)
      let (name, args) = List.assoc name env.stack in
      let extra = li |> List.map snd |> List.map expressionToBasicT in
      let residue = (name, args @ extra) in
      ((acc_pi, Cons(acc_es, Predicate residue), acc_side), Some residue)
      
      (*((True, Emp, []), Some residue)*)
    else
      let { pre = precon ; post = (post_pi, post_es, post_side); formals = arg_formal } =
        (* if functions are undefined, assume for now that they have the default spec *)
        match Env.find_fn name env with
        | None -> 
            (match Env.fine_side name env with 
            | None -> { pre = default_spec_pre; post = default_spec_post; formals = []}
            | Some (_pre, _post) ->  { pre = _pre; post = _post; formals = []}
            )
        | Some s -> s
      in
      let sb = side_binding (*find_arg_formal name env*) arg_formal arg_eff in 
      let current_state = eliminatePartiaShall (merge_spec (True, pre_es, sb) acc ) env in 


      let (res, str) = printReport current_state precon in 
      

      if res then ((And(acc_pi, post_pi), Cons (acc_es, post_es), List.append acc_side post_side), None)
      else raise (Foo ("call_function precondition fail " ^name ^":\n" ^ str ^ debug_string_of_expression fnName))
    in

    if false then begin
      Format.printf "%s:\nspec: %s@." (fnNameToString fnName) (string_of_spec spec);
      (match residue with
      | None -> print_endline "no residue"
      | Some r ->
        Format.printf "residue: %s@." (string_of_instant r));
      Format.printf "env: %s\n@." (string_of_env env)
    end;

    spec, residue


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

let rec findPolicy str_pred (policies:policy list) : (es * es) = 
  match policies with 
  | [] -> raise (Foo (str_pred ^ "'s handler is not defined!"))
  | (Eff (str, conti, afterConti))::xs  -> 
        if String.compare str str_pred == 0 then (normalES conti, normalES afterConti)
        else findPolicy str_pred xs
  | (Exn str)::xs -> if String.compare str str_pred == 0 then (Event str, Emp) else findPolicy str_pred xs 
  | (Normal es) :: xs  -> if String.compare "normal" str_pred == 0 then (es, Emp) else findPolicy str_pred xs 


let rec getEleFromListByIndex (li: event list) index: event =
  match li with
  | [] -> raise (Foo "out of index getEleFromListByIndex")
  | x::xs -> if index == 0 then x else  getEleFromListByIndex xs (index -1)

  
let rec reoccor_continue (li:((string*es)list)) (ev:string) index: int option  = 
  match li with 
  | [] -> None 
  | (x, _)::xs -> if String.compare x ev  == 0 then Some index else reoccor_continue xs ev (index + 1)

let rec sublist b e l = 
  if e < b then []
  else 
  match l with
    [] -> []
  | h :: t -> 
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail
;;

let rec string_of_list (li: 'a list ) (f : 'a -> 'b) : string = 
  match li with 
  | [] -> ""
  | x::xs-> f x ^ "," ^ string_of_list xs f ;;

let formLoop (li:((string*es)list)) start : es = 

  let (beforeLoop:es) = List.fold_left (fun acc (_, a) -> Cons (acc, a)) Emp (sublist 0 (start -1) li) in 
  
  let (sublist:es) = List.fold_left (fun acc (_, a) -> Cons (acc, a)) Emp (sublist start (List.length li) li) in 

  (*
  print_string(string_of_list (List.map (fun (_, a) -> a) li) (string_of_es) ^ "\n"^ string_of_int (List.length li) ^ "\n" ^ string_of_int (start) ^ "\n" ^string_of_es beforeLoop ^ "\n" ^ string_of_es sublist);
  
  *)
  Cons (beforeLoop, Omega sublist)

(*let rec get_the_Sequence (es:es) : (string list) list =
  match fst es  with 
  | [] -> []
  | f::_ -> 
    (match f with 
    | One str -> str :: (get_the_Sequence (derivative es f))
    | _ -> (get_the_Sequence (derivative es f))
    )
    *)

let rec get_the_Sequence (es:es) (acc:event list) : (event list) list  = 
  match fst es  with 
  | [] -> [acc]
  | fs -> 
  List.flatten(
    List.map (fun f -> 
      (match f with 

      | One _ ->  (get_the_Sequence (derivative es f) (List.append acc [f]))
      | Pred _ -> (get_the_Sequence (derivative es f) (List.append acc [f]))
       (*raise (Foo ("stack overlow recursive policy " ^ string_of_instant ins)) *)

      | _ -> (get_the_Sequence (derivative es f) acc)
      )
    ) fs 
  )



let insertMiddle acc index list_ev :event list =  

  let length = List.length acc in 
  let theFront = (sublist 0 (index - 1) acc) in  
  let theBack =  (sublist (index + 1) (length -1) acc) in  
  let result =   List.append (List.append theFront list_ev ) theBack in 
  result

let rec  nullable_plus (es:es) : bool=
  match es with
    Emp -> true
  | Bot -> false 
  | Event _ -> false 
  | Cons (es1 , es2) -> ( nullable_plus es1) && ( nullable_plus es2)
  | ESOr (es1 , es2) -> ( nullable_plus es1) || ( nullable_plus es2)
  | Kleene _ -> false
  | Underline -> false 
  | Omega _ -> false
  | Not _ -> false
  | Predicate _ -> false

;;


let rec  fst_plus (es:es): es list = 
  match es with
  | Bot -> []
  | Emp -> []
  | Event (ev) ->  [Event (ev)]
  | Not (ev) ->  [Not (ev)]
  | Cons (es1 , es2) ->  if  nullable_plus es1 then List.append ( fst_plus es1) ( fst_plus es2) else  fst_plus es1
  | ESOr (es1, es2) -> List.append ( fst_plus es1) ( fst_plus es2)
  | Kleene es1 ->  [Kleene es1]
  | Omega es1 ->  [Omega es1]
  | Underline -> [Underline]
  | Predicate (ins) -> [Predicate (ins)]

;;


let rec derivative_plus (es:es) (f:es): es =
  match (es, f) with
  | (Bot, _) -> Bot
  | (Emp, _) -> Bot
  | (Event f1, Event f2) ->  if String.compare f1 f2 == 0 then Emp else Bot 
  | (Not f1, Not f2) ->  if String.compare f1 f2 == 0 then Emp else Bot 
  | (Predicate (f1, _), Predicate (f2, _)) ->  if String.compare f1 f2 == 0 then Emp else Bot 
  | (Kleene _, Kleene _) ->  Emp 
  | (Omega _, Omega _) ->  Emp 
  | (Underline, Underline) ->  Emp 
  | (Cons (es1, es2), _) -> 
    if nullable_plus es1 
    then ESOr (derivative_plus es2 f,  Cons (derivative_plus es1 f, es2))
    else Cons (derivative_plus es1 f, es2)
  | (ESOr (es1, es2), _) -> ESOr (derivative_plus es1 f, derivative_plus es2 f )
  | _ -> Bot

;;



let rec fixpoint_compute (es:es) (policies:policy list) : es = 
  match normalES es with 
  | Predicate (ins)  -> 
    let (str_pred, _) = ins in 
    let (traceBefore, traceAfter) = findPolicy str_pred policies in 
    (* this mappings is a reversed list of Q(EFF) -> ES *)
    let rec helper (mappings:((string*es)list)) (cur_trace: es) : es =
      let cur_trace = normalES cur_trace in 
      match cur_trace with 
      | Bot -> Bot
      | Emp -> List.fold_left (fun acc (_, esLi) -> Cons(acc, esLi)) Emp (List.rev mappings)
      | _ -> let f_li = fst_plus cur_trace in 
          List.fold_left (fun acc f -> 
            let nextState () = 
              let (hd_eff, hd_es) = List.hd mappings in 
              let new_mappings = (hd_eff, Cons (hd_es, f)) :: (List.tl mappings) in 
              helper new_mappings (derivative_plus cur_trace f)
            in 
            let temp_f:es = 
              match f with 
              | Predicate (insFName, _) -> 
                (
                  match reoccor_continue (List.rev (mappings)) insFName 0 with 
                  | None -> 
                    let (contBefore, _) = findPolicy insFName policies in 
                    let new_mappings = (insFName, Emp) :: mappings in 
                    helper new_mappings (Cons (contBefore, (derivative_plus cur_trace f))) 
 
                  | Some start -> 
                    match normalES (derivative_plus cur_trace f) with 
                    | Emp -> formLoop (List.rev ( mappings)) start
                    | _ -> raise (Foo ("stack overlow recursive policy"))
                  

                )

              | Event _ -> nextState ()
              | Not _ -> nextState ()
              | Kleene _ ->  nextState ()
              | Omega _ ->  nextState ()
              | Underline -> nextState ()
              | _ -> raise (Foo "policy not possible ")
  
            in 
            ESOr(acc, temp_f)
          ) Bot f_li

    in 
    let (normalBefore, _) = findPolicy "normal" policies in 
    let fix = helper [(str_pred, Emp)] traceBefore in 
    Cons (fix, Cons (normalBefore, traceAfter))

      
   
  | Cons (es1, es2) -> Cons (fixpoint_compute es1 policies, fixpoint_compute es2 policies)
  | ESOr (es1, es2) -> ESOr (fixpoint_compute es1 policies, fixpoint_compute es2 policies)
  | Kleene es1 -> Kleene (fixpoint_compute es1 policies)
  | Omega es1 -> Omega (fixpoint_compute es1 policies)
  | _ -> es



(*
let rec fixpoint_compute (es:es) (policies:policy list) : es = 
  match normalES es with 
  | Predicate (ins)  -> 

    let (str_pred, _) = ins in 
    let trace = findPolicy str_pred policies in 
    (* this mappings is a reversed list of Q(EFF) -> ES *)
    let rec helper (mappings:((string*es)list)) (acc_event:event list) (index:int): es =
      if (List.length acc_event) <= index then 
        List.fold_left (fun acc (_, a) -> Cons (acc, a)) Emp (List.rev mappings)
      else 
        (
        match getEleFromListByIndex acc_event index with 
        | One str -> 
            let (hd_eff, hd_es) = List.hd mappings in 
            let new_mappings = (hd_eff, Cons (hd_es, Event str)) :: (List.tl mappings) in 
            helper new_mappings acc_event (index + 1)
        | Pred (curName, _) -> 
            (match reoccor_continue (List.rev (List.tl mappings)) curName 0 with 
            | Some start -> 
              if index == (List.length acc_event -1 ) then 
              formLoop (List.rev ((List.tl mappings))) start
              else raise (Foo ("stack overlow recursive policy"))
            | None -> 
              let continueation = findPolicy curName policies in 
              
              let (list_list_ev:event list list) = get_the_Sequence continueation [] in 
              
              List.fold_left (fun acc_es list_ev -> 
           
              let ((str, tempH), tempTL) = (List.hd mappings, List.tl mappings) in 
              let new_mappings = (curName, Emp) :: (str, Cons (tempH, Event (curName))) :: tempTL in 
              
              ESOr (acc_es, helper new_mappings (insertMiddle acc_event (index ) list_ev) (index ))) Bot list_list_ev
            
          )
        | _ -> raise (Foo "policy not possible ")

        )

    in 
    let traces = get_the_Sequence trace [] in 
    let res = List.fold_left (fun acc_es list_ev -> 
      ESOr (acc_es, helper [(str_pred, Emp)] list_ev 0)) 
    Bot traces in 


    res 
    

   
  | Cons (es1, es2) -> Cons (fixpoint_compute es1 policies, fixpoint_compute es2 policies)
  | ESOr (es1, es2) -> ESOr (fixpoint_compute es1 policies, fixpoint_compute es2 policies)
  | Kleene es1 -> Kleene (fixpoint_compute es1 policies)
  | Omega es1 -> Omega (fixpoint_compute es1 policies)
  | _ -> es
*)

(*
let rec expression_To_stack_content  (expr:expression): stack_content option  =
  match (expr.pexp_desc) with 
  | Pexp_ident l -> Some (Variable (getIndentName l ))
  | Pexp_constant cons ->
      (match cons with 
      | Pconst_integer (str, _) -> Some (Cons (int_of_string str))
      | _ -> None
      )
  | Pexp_apply (fnName, li) -> 
    let name = fnNameToString fnName in 
    let temp = List.map (fun (_, a) -> expression_To_stack_content a ) li in 
    let rec aux li acc =
      match acc with 
      | None -> None
      | Some acc -> (
        match li with 
        | [] -> Some acc
        | None::_ -> None
        | (Some con) :: xs -> aux xs (Some (List.append acc [con]))
      )
      
    in (match (aux temp (Some []) ) with 
    | None -> None 
    | Some li -> Some (Apply (name, li))
    )

  | _ -> None 

;;
*)

let residueToPredeciate (residue:residue):es = 
  match residue with 
  | None -> Emp
  | Some res -> Predicate res 
  ;;

(*let pre_compute_policy (policies:policy list ) : policy list = 
  let helper p : policy = 
    match p with 
    | Eff (str, es) -> 
      let rec aux esIn : es = 
        match esIn with 
        | Predicate (str_pred, _) -> 
          let rec auxaux pp : es =
            match pp with 
            | [] -> raise (Foo ("Policy is not well defined"))
            | (Eff (strIn, esIn)) ::xs  -> 
              if String.compare strIn str_pred == 0 then esIn else auxaux xs
            | _ :: xs -> auxaux xs
          in auxaux policies

        | Cons (es1, es2) -> Cons (aux es1, aux es2)
        | ESOr (es1, es2) -> ESOr (aux es1, aux es2)
        | Kleene es1 -> Kleene (aux es1)
        | Omega es1 -> Omega (aux es1)
        | _ -> esIn
      in Eff (str, aux es) 
      

    | _ -> p 

  in List.map (fun a -> 
    match helper a with 
    | Eff (str, es) -> Eff (str, normalES es)
    | _ -> helper a
    ) policies
*)

let devideContinuation (expr:expression): (expression list * expression list) = 
  let rec helper (ex:expression) : expression list = 
    match ex.pexp_desc with 
    | Pexp_sequence (ex1, ex2) -> List.append (helper (ex1)) (helper (ex2))
    | _ -> [ex]
  in let esList = helper expr in 
  let rec aux exLi before : (expression list * expression list) = 
    match exLi with 
    | [] -> (before, [])
    | x :: xs -> 
      match x.pexp_desc with 
      | (Pexp_apply (fnName, _)) -> 
        if String.compare (fnNameToString fnName) "continue" == 0 
        then 
          (
          List.append before [x], xs)
        else aux xs (List.append before [x])
      |_ -> aux xs (List.append before [x])
  in let (esLiBefore, esLiAfter) = aux esList [] in 
  (*let sequencing esLi : es = 
    List.fold_left (fun acc a -> Pexp_sequence (acc, a)) Emp esLi
  in (sequencing esLiBefore, sequencing esLiAfter)
  *)  (esLiBefore, esLiAfter) 
  ;;



let rec infer_of_expression env (pre_es:es) (acc:spec) expr : (spec * residue) =
  let getSpecFromEnv env exprIN : (es*es) = 
    let getSnd (_, a, _) = a in 
    match exprIN.pexp_desc with 
    | Pexp_apply (fnName, _) -> 
      let name = fnNameToString fnName in 
      (match Env.find_fn name env with
      | None -> 
        (match Env.fine_side name env with 
        | None -> (default_es_pre, default_es_post)
        | Some (_pre, _post) ->  (getSnd _pre, getSnd _post)
        )
      | Some s -> (getSnd s.pre, getSnd s.post)
      )
    | Pexp_ident l -> 
      let name = getIndentName l in 
      (match Env.find_fn name env with
      | None -> 
        (match Env.fine_side name env with 
        | None -> (default_es_pre, default_es_post)
        | Some (_pre, _post) ->  (getSnd _pre , getSnd _post )
        )
      | Some s -> (getSnd s.pre,getSnd s.post)
      )
    | _ -> 
      let ( (_, temp, _), _) = infer_of_expression env Emp (True, Emp, []) exprIN in 
      (default_es_pre, temp)
  in 

  match expr.pexp_desc with 
  | Pexp_fun (_, _, _ (*pattern*), expr) -> infer_of_expression env pre_es acc expr 
  | Pexp_apply (fnName, li) (*expression * (arg_label * expression) list*)
    -> 
    (*
    print_string (Pprintast.string_of_expression expr ^"\n");
    *)
    let temp = List.map (fun (_, a) -> a) li in 
    let arg_eff = List.fold_left 
    (fun acc_li a -> 
      let tuple: (es * es) = getSpecFromEnv env a in 
      
      List.append acc_li [tuple]
      ) 
    [] temp in 

    call_function pre_es fnName li acc arg_eff env
  | Pexp_let (_(*flag*),  vb_li, expr) -> 
    let head = List.hd vb_li in 
    let var_name = string_of_pattern (head.pvb_pat) in 
    let (new_acc, residue) = infer_of_expression env pre_es acc (head.pvb_expr) in 
    let stack_up = 
      (match residue with 
      | None ->
        (* print_endline ("nothing added to stack"); *)
        []
      | Some stack ->
        (* Format.eprintf "added to stack %s %s@." var_name (string_of_instant stack); *)
        [(var_name, stack)]
      ) in 
    
    infer_of_expression (Env.add_stack stack_up env) pre_es new_acc expr 

    



  | Pexp_construct _ -> 
      (acc, None)
     (*((True, Emp, []), None) *)
  | Pexp_constraint (ex, _) -> infer_of_expression env pre_es acc ex
  | Pexp_sequence (ex1, ex2) -> 

    let (acc1, _) = infer_of_expression env pre_es acc ex1 in 
    infer_of_expression env pre_es acc1 ex2

  | Pexp_match (ex, case_li) -> 
    let (spec_ex, _) = infer_of_expression env pre_es acc(*True, Emp, []*) ex in 
    let (p_ex, es_ex, side_es) = normalSpec spec_ex in 
    let rec fix_com_v2 inp_t inp_cases=
       

    in 
    let startTimeStamp = Sys.time() in
    let trace = fix_com_v2 es_ex case_li in 
    let fixpoint_time = "[Fixpoint Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]" in
    print_string (fixpoint_time);
    ((p_ex, trace, side_es) , None)



    (*
    let (policies:policy list) = List.fold_left (fun __acc a -> 
      let cuurent_p = 
        (let lhs = a.pc_lhs in 
        let rhs = a.pc_rhs in 
      
        (match lhs.ppat_desc with 
          | Ppat_effect (p1, _) -> 
            let (beforeCont, afterCont) = devideContinuation rhs in 
            let sequencing li = List.fold_left (fun _acc a -> 
           
              let ((_, es, _), _) = infer_of_expression env pre_es (True, Emp, []) a in 
              Cons (_acc, es)
              ) Emp li in 
            
            let esBefore = sequencing beforeCont in
            let esAfter = sequencing afterCont in
            [(Eff (string_of_pattern p1, normalES esBefore, normalES esAfter))]
          | Ppat_exception p1 -> [(Exn (string_of_pattern p1))]
          | _ -> 
            let ((_, es, _), _) = infer_of_expression env pre_es (True, Emp, []) rhs in
            [(Normal es)] 
        )
        )
      in List.append __acc cuurent_p
       
      ) [] case_li in 
    
    

    
    (*
    print_string (string_of_policies policies ^"\n");
    print_string (string_of_es es_ex ^"\n");
    *)

    let startTimeStamp = Sys.time() in
    let trace = fixpoint_compute es_ex policies (*pre_compute_policy policies*) in 
    let fixpoint_time = "[Fixpoint Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]" in
    print_string (fixpoint_time);
    ((p_ex, trace, side_es) , None)

*)

    
  | Pexp_ident l -> 
    
    let name = getIndentName l in 
    
    let rec aux li = 
      match li with 
      | [] -> (acc, None)
      | (str, res)::xs -> if String.compare str name == 0 then (acc, Some res) else aux xs
    in
    aux (env.stack)

  | Pexp_constant _ -> (acc, None) (*((True, Emp, []), None)*)

  (*
  | Pexp_let (_rec, bindings, c) -> 

    let env =
      List.fold_left (fun env vb ->
        let _, _, _, env, _ = infer_value_binding env vb in env) env bindings
    in

    infer_of_expression env acc c
    *)
  | Pexp_try (body, _cases) -> 
    (* TODO do cases *)
    infer_of_expression env pre_es acc body

  | Pexp_ifthenelse (_, e2, e3_op) -> 
      let (branch1, res) = infer_of_expression env pre_es acc e2 in 
      (match e3_op with 
      | None -> (branch1, res)
      | Some expr3 -> 
        let ((_, b2_es, _), _) = infer_of_expression env pre_es acc expr3 in 
        let (b1_pi, b1_es, b1_side) = branch1 in 
        ((b1_pi, ESOr (b1_es, b2_es) , b1_side), res) 
      )
      

  | _ -> raise (Foo ("infer_of_expression: " ^ debug_string_of_expression expr))

  
and infer_value_binding rec_flag env vb =
  let fn_name = string_of_pattern vb.pvb_pat in
  let body = vb.pvb_expr in
  let formals = collect_param_names body in
  let spec = 
    match function_spec body with
    | None -> default_spec_pre, default_spec_post
    | Some (pre, post) -> (normalSpec pre, normalSpec post)
  in 
  let (pre, post) = spec in
  let (pre_p, pre_es(*SYH: pre_es*, post is not including pre *), pre_side) = pre in 

  let env = Env.reset_side_spec pre_side env in 
  let env =
    match rec_flag with
    | Nonrecursive -> env
    | Recursive -> Env.add_fn fn_name {pre; post; formals} env
  in

  let ((final_pi, final_es, final_side), _ (*residue*)) =  (infer_of_expression env pre_es (pre_p, Emp, pre_side) body) in

  let final = normalSpec (final_pi, final_es (*Cons (, residueToPredeciate resdue)*), final_side) in 


(*
        (*SYH-11: This is because Prof Chin thinks the if the precondition is all the trace, it is not modular*)
        let (pre_p, pre_es, pre_side) = precon in 
        let precon = (pre_p, Cons (Kleene (Underline),pre_es), pre_side) in 
        *)

  let env1 = Env.add_fn fn_name { pre; post; formals } env in
  

  pre, post, ( final), env1, fn_name



let rec unhandled es : string option = 
  let merge a b = 
    match (a, b) with 
    | (None, None) -> None
    | (Some _, _) -> a
    | (_, Some _) -> b
  in 
  match es with 
  | Emp -> None
  | Bot -> None 
  | Event _ -> None 
  | Cons (es1 , es2) ->  merge ( unhandled es1)  ( unhandled es2)
  | ESOr (es1 , es2) -> merge ( unhandled es1)  ( unhandled es2)
  | Kleene es1 -> unhandled es1
  | Underline -> None 
  | Omega es1 -> unhandled es1
  | Not _ -> None
  | Predicate (l, _) -> Some l


let infer_of_value_binding rec_flag env vb: string * env =
  let pre, post, final, env, fn_name = infer_value_binding rec_flag env vb in
  (* don't report things like let () = ..., which isn't a function  *)
  if String.equal fn_name "()" then
    "", env
  else
    let final = normalSpec (eliminatePartiaShall final env) in
    let handling = 
      let (_, f_es, _) = final in 
      let unhandled_eff = unhandled f_es in 
      match unhandled_eff with
      | None -> ""
      | Some _ -> "" (* "\nThere is an unhandled effect: " ^ str ^ "\n"*)
    in 

    let header =
      "\n========== Function: "^ fn_name ^" ==========\n" ^
      "[Pre  Condition] " ^ string_of_spec pre ^"\n"^
      "[Post Condition] " ^ string_of_spec post ^"\n"^
      "[Final  Effects] " ^ string_of_spec (normalSpec final) ^ handling ^"\n\n"
      (*(string_of_inclusion final_effects post) ^ "\n" ^*)
      (*"[T.r.s: Verification for Post Condition]\n" ^ *)
    in
    let (_, report) = printReport final post in
    header ^ report, env


  (*

  let attributes = vb.pvb_attributes in 
  string_of_attributes attributes ^ "\n"
  *)


(* returns the inference result as a string to be printed *)
let rec infer_of_program env x: string * env =
  match x.pstr_desc with
  | Pstr_value (rec_flag, x::_ (*value_binding list*)) ->
    infer_of_value_binding rec_flag env x
    
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

  | Pstr_effect { peff_name; peff_kind; _ } ->
    begin match peff_kind with
    | Peff_decl (args, res) ->
      (* converts a type of the form a -> b -> c into ([a, b], c) *)
      let split_params_fn t =
        let rec loop acc t =
          match t.ptyp_desc with
          | Ptyp_arrow (_, a, b) ->
            (* note that we don't recurse in a *)
            loop (a :: acc) b
          | Ptyp_constr ({txt=Lident "int"; _}, [])
          | Ptyp_constr ({txt=Lident "unit"; _}, []) -> List.rev acc, t
          | _ -> failwith ("split_params_fn: " ^ debug_string_of_core_type t)
        in loop [] t
      in
      let name = peff_name.txt in
      let params = List.map core_type_to_typ args in
      let res = split_params_fn res
        |> (fun (a, b) -> (List.map core_type_to_typ a, core_type_to_typ b)) in
      let def = { params; res } in
      "", Env.add_effect name def env
    | Peff_rebind _ -> failwith "unsupported effect spec rebind"
    end
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

      (*print_string (Pprintast.string_of_structure progs ) ; 
      print_endline (List.fold_left (fun acc a -> acc ^ "\n" ^ string_of_program a) "" progs);

      *)

      let results, _ =
        List.fold_left (fun (s, env) a ->
          let spec, env1 = infer_of_program env a in
          spec :: s, env1
        ) ([], Env.empty) progs
      in
      print_endline (results |> List.rev |> String.concat "");

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

