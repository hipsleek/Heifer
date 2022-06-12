

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

let merge_spec (p1, es1, _) (p2, es2, v2) : spec = 
  [(And (p1, p2), Cons(es1, es2), v2)];;


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

let retriveStack name env = 
  let rec aux li = 
    match li with  
    | [] -> None 
    | (str, ins):: xs -> if String.compare str name == 0 then 
      Some ins else aux xs 
    in aux (env.stack)
  ;;

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

(*
let rec eliminatePartial (es:es) env :es = 
  match es with

  | Send (eff_name, arg_list) ->
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
  | Stop -> raise (Foo "eliminatePartial")

      



  ;;

let eliminatePartiaShall spec env : spec = 
  let (pi, es, side) = spec in 
  (pi, eliminatePartial es env, side);;





*)

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

let expressionToBasicT ex : basic_t option=
  match ex.pexp_desc with 
  | Pexp_constant cons ->
    (match cons with 
    | Pconst_integer (str, _) -> Some (BINT (int_of_string str))
    | _ -> None (*raise (Foo (Pprintast.string_of_expression  ex ^ " expressionToBasicT error1"))*)
    )
  | Pexp_construct _ -> Some (UNIT)
  | Pexp_ident l -> Some (VARName (getIndentName l))
  | _ -> None 
  (*
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
  *)
 
 (* | _ -> raise (Foo (Pprintast.string_of_expression  ex ^ " expressionToBasicT error2"))
*)

let rec var_binding (formal:string list) (actual: expression list) : (string * basic_t) list = 
  match (formal, actual) with 
  | (x::xs, expr::ys) -> 
    (match expressionToBasicT expr with
    | Some v ->
    (x, v) :: (var_binding xs ys)
    | None -> (var_binding xs ys)
    )
  | _ -> []
  ;;

let instantiateInstance (ins:instant) (vb:(string * basic_t) list)  : instant  = 
  let rec findbinding str vb_li =
    match vb_li with 
    | [] -> VARName str 
    | (name, v) :: xs -> if String.compare name str == 0 then v else  findbinding str xs
  in
  let rec helper li =
    match li with 
    | [] -> [] 
    | x ::xs -> 
      (
        match x with 
        | VARName str -> (findbinding str vb) :: (helper xs)
        | _ -> x :: (helper xs)
      )
  in 
  let (a, li) = ins in (a, helper li)

;;
  

let rec instantiateArg (post_es:es) (vb:(string * basic_t) list) : es = 
  match post_es with 
  | Emit ins -> Emit (instantiateInstance ins vb)
  | Await (ins, v) -> Await (instantiateInstance ins vb, v)
  | Event ins -> Event (instantiateInstance ins vb)
  | Not ins -> Not (instantiateInstance ins vb)
  | Cons (es1, es2) -> Cons (instantiateArg es1 vb, instantiateArg es2 vb)
  | ESOr (es1, es2) -> ESOr (instantiateArg es1 vb, instantiateArg es2 vb)
  | Kleene es1 -> Kleene (instantiateArg es1 vb)
  | Omega es1 -> Omega (instantiateArg es1 vb)
  | _ -> post_es
  ;;

let instantiateEff (eff:spec) (vb:(string * basic_t) list) : spec = 
  List.map (fun (p, t, v)-> (p, instantiateArg t vb, v)) eff;;

let add_es_to_spec spec es: spec = 
  List.map (fun (a, b, c) -> (a, Cons (b, es), c)) spec ;;

(*
let call_function (pre_es:es) fnName (li:(arg_label * expression) list) (acc:es) (arg_eff:(es * es) list) env (cont:es): (spec * residue) = 
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
      
      let getEffNameArg l = 
        let (_, temp) = l in 
        match temp.pexp_desc with 
        | Pexp_construct (_, argL) -> 
          (match argL with 
          | None -> []
          | Some a -> 
            match expressionToBasicT a with 
            | Some v -> [v]
            | None -> [])
        | _ -> raise (Foo "getEffNameArg error")
      in 
      let eff_name = getEffName (List.hd li) in 
      let eff_arg = getEffNameArg (List.hd li) in 

      (*
      print_string ("performing... " ^ eff_name ^ "\n" ^ string_of_int (List.length li));*)
      let eff_args = List.tl li in
      let iinnss = (eff_name,
      List.fold_left (fun acc (_, a) -> 
        match expressionToBasicT a with 
        | None -> acc
        | Some v -> List.append (acc) [v]
        ) [] eff_args) in 
      let spec = acc_pi, Cons (acc_es, Cons (Event (eff_name, eff_arg), Predicate iinnss)), acc_side in
      (* given perform Foo 1, residue is Some (Foo, [BINT 1]) *)
      let residue = Some iinnss in

      (spec, residue)
    
    else if String.compare name "continue" == 0 then 
      let (policy:spec) = List.fold_left (
        fun (acc_pi, acc_es, acc_side) (_, a_post) -> 
          (acc_pi, Cons(acc_es, a_post), acc_side)) acc arg_eff in 
      (*print_string ("contonue : " ^ string_of_spec (normalSpec (add_es_to_spec policy cont)) ^ "\n");*)
      (add_es_to_spec policy cont, None)
 
    
    else if List.mem_assoc name env.stack then
      (* higher-order function, so we should produce some residue instead *)
      let (name, args) = List.assoc name env.stack in
      let extra = (*li |> List.map snd |> List.map expressionToBasicT in *)
        List.fold_left (fun acc a -> 
          match expressionToBasicT a with 
          | None -> acc
          | Some v -> List.append (acc) [v]
        ) [] (li |> List.map snd) in 
      let residue = (name, args @ extra) in
      ((acc_pi, Cons(acc_es, Predicate residue), acc_side), Some residue)
      
      (*((True, Emp, []), Some residue)*)
    else
      let { pre = (callee_pre_pi, callee_pre_es, callee_pre_side)  ; post = (post_pi, post_es, post_side); formals = arg_formal } =
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
      let vb = var_binding arg_formal (List.map (fun (_, b) -> b) li) in 

      let post_es' = instantiateArg post_es vb in 
      let precon' = (callee_pre_pi, instantiateArg callee_pre_es vb, callee_pre_side)  in 


      let current_state = eliminatePartiaShall (merge_spec (True, pre_es, sb) acc ) env in 

      let (res, str) = printReport current_state precon' in 
      

      if res then ((And(acc_pi, post_pi), Cons (acc_es, post_es'), List.append acc_side post_side), None)
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

*)

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
  | (Exn str)::xs -> if String.compare str str_pred == 0 then (Event (str, []), Emp) else findPolicy str_pred xs 
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

let formLoop1 (li:((string*es)list)) start : es = 


  let (sublist:es) = List.fold_left (fun acc (_, a) -> Cons (acc, a)) Emp (sublist start (List.length li) li) in 

  (*
  print_string(string_of_list (List.map (fun (_, a) -> a) li) (string_of_es) ^ "\n"^ string_of_int (List.length li) ^ "\n" ^ string_of_int (start) ^ "\n" ^string_of_es beforeLoop ^ "\n" ^ string_of_es sublist);
  
  *)
  Omega sublist





let insertMiddle acc index list_ev :event list =  

  let length = List.length acc in 
  let theFront = (sublist 0 (index - 1) acc) in  
  let theBack =  (sublist (index + 1) (length -1) acc) in  
  let result =   List.append (List.append theFront list_ev ) theBack in 
  result







let rec inTheHnadlingDOm insFName policies: bool = 
  match policies with 
  | [] -> false 
  | (x, _, _) :: xs -> if String.compare insFName x == 0 then true else inTheHnadlingDOm insFName xs 
  ;;

let getEffName l = 
    let (_, temp) = l in 
    match temp.pexp_desc with 
    | Pexp_construct (a, _) -> getIndentName a 
    | _ -> raise (Foo "getEffName error")
;;
let getEffNameArg l = 
    let (_, temp) = l in 
    match temp.pexp_desc with 
    | Pexp_construct (_, argL) -> 
      (match argL with 
      | None -> []
      | Some a -> 
        match expressionToBasicT a with 
        | Some v -> [v]
        | None -> [])
    | _ -> raise (Foo "getEffNameArg error")
;;

let rec findNormalReturn handler = 
  match handler with 
  | [] -> raise (Foo "could not find the normal retrun")
  | a::xs -> 
    let lhs = a.pc_lhs in 
    let rhs = a.pc_rhs in 
    (match lhs.ppat_desc with 
    | Ppat_effect (_, _) 
    | Ppat_exception _   -> findNormalReturn xs 
    | _ -> rhs
    )
  ;;

let concatenateEffects (eff1:spec) (eff2:spec) : spec = 
  let zip = List.combine eff1 eff2 in 
  List.map (fun ((p1, es1, _), (p2, es2, v2)) -> (And(p1, p2), Cons (es1, es2), v2)) zip ;;


let rec findEffectHanding handler name = 
  match handler with 
  | [] -> raise (Foo "could not find the findEffectHanding")
  | a::xs -> 
    let lhs = a.pc_lhs in 
    let rhs = a.pc_rhs in 
    (match lhs.ppat_desc with 
    | Ppat_effect (p, _) 
    | Ppat_exception p   -> if String.compare (string_of_pattern p) name == 0 then rhs else findEffectHanding xs  name 
    | _ -> findEffectHanding xs  name
    )
  ;;



let replacePlaceholder originEff ins newEff : spec = 
  let rec aux t_original t_new :es = 
    match t_original with 
    | Await (ins1, _) -> if compareInstant ins1 ins then t_new else t_original
    | Cons (es1, es2)-> Cons (aux es1 t_new, aux es2 t_new)
    | ESOr  (es1, es2)-> ESOr (aux es1 t_new, aux es2 t_new)
    | Kleene es1 -> Kleene (aux es1 t_new)
    | Infiny es1 -> Infiny (aux es1 t_new)
    | Omega es1 -> Omega (aux es1 t_new)
    | _ -> t_original 

  in 
  let zip = List.combine originEff newEff in 
  List.map (fun ((p, t, v), (p1, t1, _)) -> (And(p, p1), aux t t1, v)) zip
        
  
;;

let concatnateEffEs eff es : spec = 
  List.map (fun (p, t, v) -> (p, Cons (t, es), v)) eff;;

let rec infer_handling env handler ins (current:spec) (der:es) (expr:expression): spec = 
  match expr.pexp_desc with 
  | Pexp_fun (_, _, _ (*pattern*), exprIn) -> 
    infer_handling env handler ins current der exprIn

(* VALUE *)   
  | Pexp_constant cons ->
    (match cons with 
    | Pconst_integer (str, _) -> 
      List.map (fun (p, t, _) -> (p, t, BINT (int_of_string str))) current
    | _ -> raise (Foo (Pprintast.string_of_expression  expr ^ " expressionToBasicT error1"))
    )
  | Pexp_construct _ -> List.map (fun (p, t, _) -> (p, t, UNIT)) current
  | Pexp_ident l -> List.map (fun (p, t, _) -> (p, t, VARName (getIndentName l))) current 
   
  | Pexp_apply (fnName, li) -> 
    let name = fnNameToString fnName in 
    if String.compare name "continue" == 0 then 
(* CONTINUE *)
      let (_, continue_value) = (List.hd (List.tl li)) in 
      let eff_value = infer_of_expression env [(True, Emp, UNIT)] continue_value in 

      List.flatten (
        List.map (fun (p, t, v) -> 
          let updatedEff = (replacePlaceholder [(p, der, v)] ins eff_value) in 
          List.flatten (List.map (fun a -> fixCompute env t handler a) updatedEff) 
        ) current 
      )

    else if String.compare name "perform" == 0 then 
      let eff_name = getEffName (List.hd li) in 
      let eff_arg = getEffNameArg (List.hd li) in 
      List.map (fun (p, t, v) -> (p, (Cons(t, Emit (eff_name, eff_arg))), v) 
      ) current

      
    else  raise (Foo "infer_handling not yet covering functiin calls")
    
  | Pexp_sequence (ex1, ex2) -> 
    (match ex1.pexp_desc with
    | Pexp_apply (fnName, li) -> 
      let name = fnNameToString fnName in 
      if String.compare name "continue" == 0 then 
(* CONTINUE *)
        let (_, continue_value) = (List.hd (List.tl li)) in 
        let eff_value = infer_of_expression env [(True, Emp, UNIT)] continue_value in 
        let newEff = List.flatten (
          List.map (fun (p, t, v) -> 
            let updatedEff = (replacePlaceholder [(p, der, v)] ins eff_value) in 
            List.flatten (List.map (fun a -> fixCompute env t handler a) updatedEff) 
          ) current 
        ) in 
        infer_handling env handler ins newEff der ex2

  

      else if String.compare name "perform" == 0 then 
        let eff_name = getEffName (List.hd li) in 
        let eff_arg = getEffNameArg (List.hd li) in 
        List.flatten (
          List.map (fun (p, t, v) ->
            infer_handling env handler ins [(p, (Cons(t, Emit (eff_name, eff_arg))), v)] der ex2
          ) current
        )

      
      else 
        let eff1 = infer_handling env handler ins current der ex1 in 
        infer_handling env handler ins eff1 der ex2
    | _ -> raise (Foo "not yet here")
    )



  | _ -> raise (Foo "not yet covered infer_handling")
    (*infer_of_expression env current expr*)




and  fixCompute env (history:es) handler (p, t, v) : spec = 
  match (normalES t) with 
  | Stop -> 
    let (normalExpr:expression) = findNormalReturn handler in 
    infer_of_expression env [(p, history, v)] normalExpr
     
  
  | _ -> 
    let fstSet = fst t in 

    List.flatten (List.map ( fun f ->
      match f with
      | Send (ins) -> 
        let (effName, _) = ins in 
        let expr = (findEffectHanding handler effName) in 
        infer_handling env handler ins [(p, Cons(history, Event ins), v)] (derivative t f)  expr     
      | _ ->  fixCompute env (Cons (history, eventToEs f)) handler (p, derivative t f, v)
    ) fstSet)




and fixpoint_Computation env handler eff : spec = 
  List.flatten (List.map (fun tuple-> fixCompute env Emp handler tuple) eff)


and infer_of_expression (env) (current:spec) expr: spec =  
  match expr.pexp_desc with 
  | Pexp_fun (_, _, _ (*pattern*), exprIn) -> 
    infer_of_expression env current exprIn

(* VALUE *)
  | Pexp_constant cons ->
    (match cons with 
    | Pconst_integer (str, _) -> List.map (fun (p, t, _) -> (p, t, BINT (int_of_string str)) ) current  
    | _ -> raise (Foo (Pprintast.string_of_expression  expr ^ " expressionToBasicT error1"))
    )
  | Pexp_construct _ -> List.map (fun (p, t, _) -> (p, t, UNIT) ) current
  | Pexp_ident l -> List.map (fun (p, t, _) -> (p, t, VARName (getIndentName l)) ) current
    
(* CONDITIONAL not path sensitive so far *)
  | Pexp_ifthenelse (_, e2, e3_op) ->  
    let branch1 = infer_of_expression env current e2 in 
    (match e3_op with 
    | None -> branch1
    | Some expr3 -> 
      let branch2 = infer_of_expression env current expr3 in 
      List.append branch1 branch2)

  | Pexp_let (_(*flag*),  vb_li, exprIn) -> 
    let head = List.hd vb_li in 
    let var_name = string_of_pattern (head.pvb_pat) in 
    (match (head.pvb_expr.pexp_desc) with 
    | Pexp_apply (fnName, li) -> 
      let name = fnNameToString fnName in 
      if String.compare name "perform" == 0 then 
(* PERFORM *)
        let eff_name = getEffName (List.hd li) in 
        let eff_arg = getEffNameArg (List.hd li) in 
        infer_of_expression (Env.add_stack [(var_name, (eff_name, eff_arg))] env) (List.map (fun (p, t, v)-> (p, Cons(t, Emit (eff_name, eff_arg)), v)) current) exprIn
      else (match (retriveStack name env) with
          | Some ins -> 
(* CALL-PLACEHOLDER *)
            let (_, arg) = List.hd li in  
            (match expressionToBasicT (arg) with 
            | Some eff_arg ->  infer_of_expression env 
                  (List.map (fun (p, t, v)-> (p, Cons(t, Await (ins, eff_arg )), v)) current) exprIn
            | None -> raise (Foo ("Placeholder has no argument")))

          | None -> 
(* FUNCTION-CALL *)
let { pre = pre  ; post = post; formals = arg_formal } =
(* if functions are undefined, assume for now that they have the default spec *)
match Env.find_fn name env with
| None -> { pre = default_spec_pre; post = default_spec_post; formals = []}
| Some s -> s
      in
      let vb = var_binding arg_formal (List.map (fun (_, b) -> b) li) in 

      let postcon' = instantiateEff post vb in 
      let precon' = instantiateEff pre vb in 


      let (res, str) = printReport current precon' in 
      

      if res then concatenateEffects current postcon'
       else raise (Foo ("call_function precondition fail " ^name ^":\n" ^ str ^ debug_string_of_expression fnName))

               
            )
        
    

    | _ -> raise (Foo "Let error")
    )

  | Pexp_match (ex, case_li) -> 
    let ex_eff = normalSpec (infer_of_expression env [(True, Emp, UNIT)] ex) in 
    let eff_fix = fixpoint_Computation env case_li (concatnateEffEs ex_eff Stop) in 
    concatenateEffects current eff_fix 

  | Pexp_sequence (ex1, ex2) -> 
    let eff1 = infer_of_expression env current ex1 in 
    infer_of_expression env eff1 ex2 
  
(* Aplications *)
  | Pexp_apply (fnName, li) -> 
      let name = fnNameToString fnName in 
      if String.compare name "perform" == 0 then 
(* PERFORM *)
        let eff_name = getEffName (List.hd li) in 
        let eff_arg = getEffNameArg (List.hd li) in 
        (List.map (fun (p, t, v)-> (p, Cons(t, Emit (eff_name, eff_arg)), v)) current)
      else (match (retriveStack name env) with
          | Some ins -> 
(* CALL-PLACEHOLDER *)
            let (_, arg) = List.hd li in  
            (match expressionToBasicT (arg) with 
            | Some eff_arg ->  
                  (List.map (fun (p, t, v)-> (p, Cons(t, Await (ins, eff_arg )), v)) current)
            | None -> raise (Foo ("Placeholder has no argument")))

          | None -> 
(* FUNCTION-CALL *)
let { pre = pre  ; post = post; formals = arg_formal } =
(* if functions are undefined, assume for now that they have the default spec *)
match Env.find_fn name env with
| None -> { pre = default_spec_pre; post = default_spec_post; formals = []}
| Some s -> s
      in
      let vb = var_binding arg_formal (List.map (fun (_, b) -> b) li) in 

      let postcon' = instantiateEff post vb in 
      let precon' = instantiateEff pre vb in 


      let (res, str) = printReport current precon' in 
      

      if res then concatenateEffects current postcon'
       else raise (Foo ("call_function precondition fail " ^name ^":\n" ^ str ^ debug_string_of_expression fnName))

            
         
            
            )
        


  | _ -> raise (Foo (Pprintast.string_of_expression  expr ^ " infer_of_expression not corvered "))  


(*
let rec infer_of_expression env (current:spec) expr: spec = 

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
      let ( (_, temp, _), _) = infer_of_expression env Emp (True, Emp, []) exprIN cont in 
      (default_es_pre, temp)
  in 

  match expr.pexp_desc with 
  | Pexp_fun (_, _, _ (*pattern*), exprIn) -> 
    infer_of_expression env pre_es acc exprIn cont
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

    call_function pre_es fnName li acc arg_eff env cont 
  | Pexp_let (_(*flag*),  vb_li, expr) -> 
    let head = List.hd vb_li in 
    let var_name = string_of_pattern (head.pvb_pat) in 
    let (new_acc, residue) = infer_of_expression env pre_es acc (head.pvb_expr) cont in 
    let stack_up = 
      (match residue with 
      | None ->
        (* print_endline ("nothing added to stack"); *)
        []
      | Some stack ->
        (* Format.eprintf "added to stack %s %s@." var_name (string_of_instant stack); *)
        [(var_name, stack)]
      ) in 
    
    
    infer_of_expression (Env.add_stack stack_up env) pre_es new_acc expr cont


  | Pexp_construct _ -> 
      (acc, None)
     (*((True, Emp, []), None) *)
  | Pexp_constraint (ex, _) -> infer_of_expression env pre_es acc ex cont
  | Pexp_sequence (ex1, ex2) -> 

    let (acc1, _) = infer_of_expression env pre_es acc ex1 cont in 
    infer_of_expression env pre_es acc1 ex2 cont

  | Pexp_match (ex, case_li) -> 
    let (spec_ex, _) = infer_of_expression env pre_es acc(*True, Emp, []*) ex cont in 
    let (p_ex, es_ex, side_es) = normalSpec spec_ex in 

    (* VERSION 3 *)
    let policies = List.map (fun a ->
      let lhs = a.pc_lhs in 
      let rhs = a.pc_rhs in 
      
      (match lhs.ppat_desc with 
      | Ppat_effect (p1, _) 
      | Ppat_exception p1   -> 
        let (beforeCont, afterCont) = devideContinuation rhs in 
        (string_of_pattern p1, beforeCont, afterCont)
      | _ -> 
        let (beforeCont, afterCont) = devideContinuation rhs in 
        ("normal", beforeCont, afterCont)
      )
    ) case_li in 
    let rec find_policy_before ((name, _) as i) li = 
      match li with 
      | [] -> []
      | (str, before, _) :: xs -> if String.compare str name == 0 then before else find_policy_before i xs
    in 
    let rec find_policy_after name li =
      match li with 
      | [] -> raise (Foo (name ^ "'s handler is not defined\n"))
      | (str, _, after) :: xs -> if String.compare str name == 0 then after else find_policy_after name xs
    in 
    let sequencing li cont'= List.fold_left (fun _acc a -> 
            let ((_, es, _), _) = infer_of_expression env pre_es (True, Emp, []) a cont' in 
            Cons (_acc, es)
            ) Emp li in 

    let rec going_through_f_spec f_es mappings current stack: es = 
      match (normalES f_es) with
      | Kleene f_es_In -> Kleene (going_through_f_spec f_es_In mappings current stack)
      | Omega f_es_In -> Omega (going_through_f_spec f_es_In mappings current stack)
      | Cons (Kleene f_es_In, f_es_rhs) -> 
        let a = Kleene (going_through_f_spec f_es_In mappings current stack) in 
        let b = (going_through_f_spec f_es_rhs mappings current stack) in 
        Cons (a, b)
      | Cons (Omega f_es_In, f_es_rhs) -> 
        let a = Omega (going_through_f_spec f_es_In mappings current stack) in 
        let b = (going_through_f_spec f_es_rhs mappings current stack) in 
        Cons (a, b)
  
      (*| ESOr (es1, es2) -> 
        let a = (going_through_f_spec es1 mappings current) in 
        let b = (going_through_f_spec es2 mappings current) in 
        ESOr (a, b)
        *)

      | _ -> 
      (*
      print_string (
        List.fold_left (fun acc (a, b) -> acc ^ "\n" ^ a ^ ": " ^ string_of_es (normalES b) ) "\n===\n" (List.append mappings [current]) ^ "\n"
      );
      *)

      let normal_es = sequencing (find_policy_before ("normal", []) policies) Emp in 

      let fsts = fst f_es in 
      let disjunctions = List.map (fun f -> 
        match f with
        | StopEv -> 
          print_string ("hshshhshs " ^ string_of_int (List.length stack)^ "\n");
          let state_traces = sequencing (List.rev stack) Emp in 
          Cons (normal_es, state_traces) 
        | One str ->  
          let (cur_str, cur_es) =  current in 
          let expre_li = find_policy_before str policies in 
          let es_expr_li = going_through_f_spec(sequencing expre_li Emp) [] ("null", Emp) stack in 
          let new_current = (cur_str, Cons (Cons (cur_es, Event str), es_expr_li)) in 
          Cons (Cons (Event str, es_expr_li), going_through_f_spec (derivative f_es f) mappings new_current stack)
        | Zero str -> 
          let (cur_str, cur_es) =  current in 
          let new_current = (cur_str, Cons (cur_es, Not str)) in 
          Cons (Not str, going_through_f_spec (derivative f_es f) mappings new_current stack) 
        | Any -> 
          let (cur_str, cur_es) =  current in  
          let new_current = (cur_str, Cons (cur_es, Underline)) in 
          Cons (Underline, going_through_f_spec (derivative f_es f) mappings new_current stack) 
        | Pred (ins) -> 
          let (insFName, _) = ins in 
          if inTheHnadlingDOm insFName policies  == false then
            let (cur_str, cur_es) =  current in  
            let new_current = (cur_str, Cons (cur_es, Predicate ins)) in 
            Cons (Predicate ins, going_through_f_spec (derivative f_es f) mappings new_current stack)
          else 
          let new_mapping = List.append mappings [current] in 
          let new_current = (insFName, Emp) in 

          match reoccor_continue (new_mapping) insFName 0 with 
          | Some start -> formLoop1 ( new_mapping) start
          | None -> 


          let expre_li = find_policy_after insFName policies in 
          if List.length expre_li == 0 then Emp 
          else 

            let continue_k = normalES (derivative f_es f) in 
            let cont = List.hd expre_li in
            let after_cont = List.tl expre_li in 
            let ((_, fixpoint_trace_insert, _), _) = infer_of_expression env pre_es (True, Emp, []) cont Emp in 
            (*
            print_string ("to print the effects of the continue: \n" ^ string_of_es (normalES fixpoint_trace_insert) ^"\n");
            *)
            let insterting = going_through_f_spec fixpoint_trace_insert new_mapping new_current stack in 
            (*
            print_string ("to print the effects of the continue1: \n" ^ string_of_es (normalES insterting) ^"\n");
            *)
            let insterting2 = going_through_f_spec continue_k [] ("null", Emp) (List.append stack after_cont) in  

(************************************************** After the first continue 
            let partitions = partitionContinue after_cont in 
            let partitionTraces = List.map ( fun partition -> 
              if List.length partition == 0 then Emp 
              else 
                let contP = List.hd partition in
                let after_contP = List.tl partition in 
                let ((_, fixpoint_trace_insertP, _), _) = infer_of_expression env pre_es (True, Emp, []) contP Emp in 
                let instertingP = going_through_f_spec fixpoint_trace_insertP new_mapping new_current in 
                let insterting2P = going_through_f_spec continue_k [] ("null", Emp) in  
                let trace_after_instertP = sequencing after_contP continue_k in 

                Cons (instertingP, Cons (insterting2P, trace_after_instertP))


            ) partitions in 
            let trace_after_instert = List.fold_left (fun acc a -> Cons (acc, a)) Emp partitionTraces in 


************************************************* After the first continue *)


            (*
            print_string (string_of_int (List.length partitions) ^ ") -> trace after: " ^ string_of_es (normalES trace_after_instert)^ "\n");
                        print_string ("normal trace: " ^ string_of_es (normalES normal_es)^ "\n");

            *)
            Cons(insterting, insterting2)


      ) fsts in 
      if List.length fsts == 0 then Emp else 
      List.fold_left (fun acc a -> ESOr (acc,  a)) Bot disjunctions 
    in 
    let startTimeStamp = Sys.time() in
    print_string ((*string_of_int (List.length case_li)^*) "\n=============== \n ");
    let trace = going_through_f_spec (Cons (es_ex, Stop)) [] ("null", Emp) []in 
    let fixpoint_time = "[Fixpoint Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]" in
    print_string (fixpoint_time);
    ((p_ex, trace, side_es) , None)


    


  | Pexp_try (body, _cases) -> 
    (* TODO do cases *)
    infer_of_expression env pre_es acc body cont


      

  | _ -> raise (Foo ("infer_of_expression: " ^ debug_string_of_expression expr))
*)
  
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

  (*let env = Env.reset_side_spec pre_side env in  *)
  let env =
    match rec_flag with
    | Nonrecursive -> env
    | Recursive -> Env.add_fn fn_name {pre; post; formals} env
  in

  let final =  (infer_of_expression env pre body) in

  let final = normalSpec final in 


(*
        (*SYH-11: This is because Prof Chin thinks the if the precondition is all the trace, it is not modular*)
        let (pre_p, pre_es, pre_side) = precon in 
        let precon = (pre_p, Cons (Kleene (Underline),pre_es), pre_side) in 
        *)

  let env1 = Env.add_fn fn_name { pre; post; formals } env in
  

  pre, post, ( final), env1, fn_name





let infer_of_value_binding rec_flag env vb: string * env =
  let pre, post, final, env, fn_name = infer_value_binding rec_flag env vb in
  (* don't report things like let () = ..., which isn't a function  *)
  if String.equal fn_name "()" then
    "", env
  else

    let header =
      "\n========== Function: "^ fn_name ^" ==========\n" ^
      "[Pre  Condition] " ^ string_of_spec pre ^"\n"^
      "[Post Condition] " ^ string_of_spec post ^"\n"^
      "[Final  Effects] " ^ string_of_spec (normalSpec final) ^"\n\n"
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
      print_endline "\nERROR:\n";
      print_endline s
    | e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;

