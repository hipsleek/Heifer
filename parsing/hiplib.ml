

open Hipprover
open Hipcore
module Pretty = Pretty
module Debug = Debug
module Common = Hiptypes
exception Foo of string
open Ocamlfrontend
open Parsetree
open Asttypes
(* get rid of the alias *)
type string = label
(* open Rewriting *)
open Pretty
open Debug
open Hiptypes
open Normalize

let file_mode = ref false
let test_mode = ref false
let tests_failed = ref false

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;



let rec shaffleZIP li1 li2 = 
  let rec aux a li = 
    match li with 
    | []-> []
    | y :: ys -> (a, y) :: (aux a ys)
  in 
  match li1 with 
  | [] -> []
  | x ::xs -> List.append (aux x li2) (shaffleZIP xs li2) 
;;


assert ((List.length (shaffleZIP [1;2;3] [4;5;6])) = 9 );;

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
  | Ptyp_tuple (ctLi) -> "(" ^
    (List.fold_left (fun acc a -> acc ^ "," ^ string_of_core_type a ) "" ctLi) ^ ")"

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
  | Ppat_construct (l, Some _p1) ->  
    List.fold_left (fun acc a -> acc ^ a) "" (Longident.flatten l.txt)
    (* ^ string_of_pattern p1 *)
  (* #tconst *)

  
  | _ -> Format.asprintf "string_of_pattern: %a\n" Pprintast.pattern p;;

let findFormalArgFromPattern (p): string list =
  match p.ppat_desc with 
  | Ppat_construct (_, None) -> []
  | Ppat_construct (_, Some _p1) -> 
    (match _p1.ppat_desc with
    | Ppat_tuple p1 -> List.map (fun a -> string_of_pattern a) p1
    | _ -> [string_of_pattern _p1]
    )

  | _ -> []

let rec get_tactic e =
  match e with
  | { pexp_desc = Pexp_ident { txt = Lident "unfold_right"; _ }; _ } ->
    [Unfold_right]
  | { pexp_desc = Pexp_ident { txt = Lident "unfold_left"; _ }; _ } ->
    [Unfold_left]
  | { pexp_desc = Pexp_apply ({pexp_desc = Pexp_ident { txt = Lident "apply"; _ }; _}, [(_, {pexp_desc = Pexp_ident { txt = Lident lem; _ }; _})]); _ } ->
    [Apply lem]
  | { pexp_desc = Pexp_apply ({pexp_desc = Pexp_ident { txt = Lident "case"; _ }; _}, [(_, {pexp_desc = Pexp_constant (Pconst_integer (i, _)); _}); (_, sub)]); _ } ->
    let t = List.hd (get_tactic sub) in
    [Case (int_of_string i, t)]
  | { pexp_desc = Pexp_sequence (e1, e2); _ } ->
    let a = get_tactic e1 in
    let b = get_tactic e2 in
    a @ b
  | _ -> []

let collect_annotations attrs =
  List.fold_right
    (fun c t ->
      match c.attr_payload with
      | PStr [{ pstr_desc = Pstr_eval (e, _); _ }] when String.equal "proof" c.attr_name.txt -> get_tactic e
      | _ -> t)
    attrs []

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
      | Pexp_constraint (e, _t) ->
        (* ignore constraints *)
        traverse_to_body e
      | Pexp_fun (_, _, name, body) ->
        let name =
          match name.ppat_desc with
          | Ppat_var s -> [s.txt]
          | Ppat_constraint (p, _ ) -> 
            (
              match p.ppat_desc with
              | Ppat_var s -> [s.txt]
              | _ -> raise (Foo "collect_param_names other type")
            )
          
          | _ ->
            (* dummy name for things like a unit pattern, so we at least have the same number of parameters *)
            [verifier_getAfreeVar "dummy"]
            (* we don't currently recurse inside patterns to pull out variables, so something like
              let f () (Foo a) = 1
              will be treated as if it has no formal params. *)
        in
        let ns, body = traverse_to_body body in
        name @ ns, body
      | _ -> ([], e)
    in
    traverse_to_body rhs

let rec string_of_effectList (specs:spec list):string =
  match specs with 
  | [] -> ""
  | x :: xs -> string_of_spec x ^ " /\\ "^  string_of_effectList xs 


let string_of_effectspec spec:string =
    match spec with
    | None -> "<no spec given>"
    (* | Some (pr, po) ->
      Format.sprintf "requires %s ensures %s" (string_of_spec pr) (string_of_effectList po) *)
    | Some p -> string_of_spec p


let debug_string_of_expression e =
  Format.asprintf "%a" (Printast.expression 0) e

let string_of_longident l =
  l |> Longident.flatten |> String.concat "."


let rec getIndentName (l:Longident.t): string = 
  (match l with 
        | Lident str -> str
        | Ldot (t, str) -> getIndentName t ^ "." ^ str
        | _ -> "getIndentName: dont know " ^ string_of_longident l
        )
        ;;

(* information we record after seeing a function *)
type fn_spec = {
  pre: spec;
  post: spec list;
  formals: string list;
}


(* at a given program point, this captures specs for all local bindings *)
type fn_specs = fn_spec SMap.t

(* only first-order types for arguments, for now *)
type typ = 
    TInt 
  | TUnit 
  | TRef of typ 
  | TString 
  | TTuple of (typ list) 
  | TArrow of (typ * typ)

let rec core_type_to_typ (t:core_type) =
  match t.ptyp_desc with
  | Ptyp_constr ({txt=Lident "int"; _}, []) -> TInt
  | Ptyp_constr ({txt=Lident "unit"; _}, []) -> TUnit
  | Ptyp_constr ({txt=Lident "string"; _}, []) -> TString
  | Ptyp_constr ({txt=Lident "ref"; _}, [t]) -> TRef (core_type_to_typ t)
  | Ptyp_tuple (tLi) -> TTuple (List.map (fun a -> core_type_to_typ a) tLi)
  | Ptyp_arrow (_, t1, t2) -> TArrow (core_type_to_typ t1, core_type_to_typ t2)
  
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
  effect_defs : effect_def SMap.t;
}

type function_without_spec = (string * expression * string list)
let (env_function_without_spec: ((function_without_spec list)ref)) = ref [] 

let rec retrieveFuntionWithoutSpecDefinition str li = 
  match li with 
  | [] ->  None 
  | (s, b, f) :: xs  -> if String.compare s str == 0 then (Some (s, b, f)) 
  else retrieveFuntionWithoutSpecDefinition str xs 


let rec string_of_basic_v li: string = 
  match li with 
  | [] -> ""
  | (str, bt) :: xs ->(str ^ "=" ^ string_of_term bt  ^ ", ") ^ string_of_basic_v xs 


module Env = struct
  let empty = {
    modules = SMap.empty;
    current = SMap.empty;
    effect_defs = SMap.empty
  }

  let add_fn f spec env =
    { env with current = SMap.add f spec env.current }

  let add_effect name def env =
    { env with effect_defs = SMap.add name def env.effect_defs }

  let find_fn f env =
    SMap.find_opt f env.current
  
  
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
        (string_of_spec (List.hd s.post))
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
      | Some (pre, post) -> Some {pre =  pre; post =  post; formals = []}
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


  

let fnNameToString fnName: string = 
  match fnName.pexp_desc with 
    | Pexp_ident l -> getIndentName l.txt 
        
    | _ -> "fnNameToString: dont know " ^ debug_string_of_expression fnName
    ;;








let getEffName l = 
    let (_, temp) = l in 
    match temp.pexp_desc with 
    | Pexp_construct (a, _) -> getIndentName a.txt 
    | _ -> raise (Foo "getEffName error")
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
    | _ ->     
      ("v", rhs))
  ;;


let rec findEffectHanding handler name = 
  match handler with 
  | [] -> None 
  | a::xs -> 
    let lhs = a.pc_lhs in 
    let rhs = a.pc_rhs in 
    (match lhs.ppat_desc with 
    | Ppat_effect (p, _) -> 
      if String.compare (string_of_pattern p) name == 0 
      then 
        let formalArg = findFormalArgFromPattern p in 
        (Some (rhs, formalArg)) 
      else findEffectHanding xs  name
    | Ppat_exception p -> if String.compare (string_of_pattern p) name == 0 then (Some (rhs, [])) else findEffectHanding xs  name 
    | _ -> findEffectHanding xs  name
    )
  ;;
     
  
;;

let string_of_expression_kind (expr:Parsetree.expression_desc) : string = 
  match expr with 
  | Pexp_ident _ -> "Pexp_ident"
  | Pexp_constant _ -> "Pexp_constant"
  | Pexp_let _ -> "Pexp_let"
  | Pexp_function _ -> "Pexp_function"
  | Pexp_fun _ -> "Pexp_fun"
  | Pexp_apply _ -> "Pexp_apply"
  | Pexp_match _ -> "Pexp_match"
  | Pexp_try _ -> "Pexp_try"
  | Pexp_tuple _ -> "Pexp_tuple"
  | Pexp_construct _ -> "Pexp_construct"
  | Pexp_variant _ -> "Pexp_variant"
  | Pexp_record _ -> "Pexp_record"
  | Pexp_field _ -> "Pexp_field"
  | Pexp_setfield _ -> "Pexp_setfield"
  | Pexp_array _ -> "Pexp_array"
  | Pexp_ifthenelse _ -> "Pexp_ifthenelse"
  | Pexp_sequence _ -> "Pexp_sequence"
  | Pexp_while _ -> "Pexp_while"
  | Pexp_for _ -> "Pexp_for"
  | Pexp_constraint _ -> "Pexp_constraint"
  | Pexp_coerce _ -> "Pexp_coerce"
  | Pexp_send _ -> "Pexp_send"
  | Pexp_new _ -> "Pexp_new"
  | Pexp_setinstvar _ -> "Pexp_setinstvar"
  | Pexp_override _ -> "Pexp_override"
  | Pexp_letmodule _ -> "Pexp_letmodule"
  | Pexp_letexception _ -> "Pexp_letexception"
  | Pexp_assert _ -> "Pexp_assert"
  | Pexp_lazy _ -> "Pexp_lazy"
  | Pexp_poly _ -> "Pexp_poly"
  | Pexp_object _ -> "Pexp_object"
  | Pexp_newtype _ -> "Pexp_newtype"
  | Pexp_pack _ -> "Pexp_pack"
  | Pexp_open _ -> "Pexp_open"
  | Pexp_letop _ -> "Pexp_letop"
  | Pexp_extension _ -> "Pexp_extension"
  | Pexp_unreachable -> "Pexp_unreachable"

let rec getLastEleFromList li = 
  match li with 
  | [] -> raise (Foo "getLastEleFromList impossible")
  | [x] -> x 
  | _ :: xs -> getLastEleFromList xs 

let deleteTailSYH  (li:'a list) = 
  let rec aux liIn acc =
    match liIn with 
    | [] -> raise (Foo "deleteTailSYH impossible")
    | [_] -> acc 
    | x :: xs -> aux xs (List.append acc [x])
  in aux li []


let is_ident name e =
  match e.pexp_desc with
  | Pexp_ident {txt=Lident i; _} when name = i -> true
  | _ -> false

open Forward_rules

let rec expr_to_term (expr:expression) : term =
  match expr.pexp_desc with
  | Pexp_constant (Pconst_integer (i, _)) -> Num (int_of_string i)
  | Pexp_ident {txt=Lident i; _} -> Var i
  | Pexp_apply ({pexp_desc = Pexp_ident {txt=Lident i; _}; _}, [(_, a); (_, b)]) ->
      begin match i with
      | "+" -> Plus (expr_to_term a, expr_to_term b)
      | "-" -> Minus (expr_to_term a, expr_to_term b)
      | _ -> failwith (Format.asprintf "unknown op %s" i)
      end
  | _ -> failwith (Format.asprintf "unknown term %a" Pprintast.expression expr)

let rec expr_to_formula (expr:expression) : pi * kappa =
  match expr.pexp_desc with
  | Pexp_apply ({pexp_desc = Pexp_ident {txt=Lident i; _}; _}, [(_, a); (_, b)]) ->
      begin match i with
      | "=" ->
        (* !i=a is allowed as shorthand for i-->a, but equalities between pointer values, e.g. !i=!j, are not generally allowed. they can be expressed using let v=!i in assert (!j=v). *)
        begin match a.pexp_desc, b.pexp_desc with
        | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident "!"; _}); _}, [_, {pexp_desc = Pexp_ident {txt=Lident p; _}; _}]), _ ->
          True, PointsTo (p, expr_to_term b)
        | _ ->
          Atomic (EQ, expr_to_term a, expr_to_term b), EmptyHeap
        end
      | "<" -> Atomic (LT, expr_to_term a, expr_to_term b), EmptyHeap
      | "<=" -> Atomic (LTEQ, expr_to_term a, expr_to_term b), EmptyHeap
      | ">" -> Atomic (GT, expr_to_term a, expr_to_term b), EmptyHeap
      | ">=" -> Atomic (GTEQ, expr_to_term a, expr_to_term b), EmptyHeap
      | "&&" ->
        let p1, h1 = expr_to_formula a in
        let p2, h2 = expr_to_formula b in
        And (p1, p2), SepConj (h1, h2)
      | "=>" ->
        let p1, _h1 = expr_to_formula a in
        let p2, _h2 = expr_to_formula b in
        Imply (p1, p2), EmptyHeap (* no magic wand *)
      | "||" ->
        let p1, _h1 = expr_to_formula a in
        let p2, _h2 = expr_to_formula b in
        Or (p1, p2), EmptyHeap (* heap disjunction is not possible *)
      | "-->" ->
        let v =
          match expr_to_term a with
          | Var s -> s
          | _ -> failwith (Format.asprintf "invalid lhs of points to: %a" Pprintast.expression a)
        in
        True, PointsTo (v, expr_to_term b)
      | _ ->
        failwith (Format.asprintf "unknown binary op: %s" i)
      end
  | Pexp_apply ({pexp_desc = Pexp_ident {txt=Lident i; _}; _}, [(_, _a)]) ->
      begin match i with
      (* | "not" -> Not (expr_to_formula a) *)
      | _ -> failwith (Format.asprintf "unknown unary op: %s" i)
      end
  | Pexp_construct ({txt=Lident "true"; _}, None) -> True, EmptyHeap
  | Pexp_construct ({txt=Lident "false"; _}, None) -> False, EmptyHeap
  | _ ->
    failwith (Format.asprintf "unknown kind of formula: %a" Pprintast.expression expr)


(** see [transform_str] for what env is *)
let rec transformation (env:string list) (expr:expression) : core_lang =
  match expr.pexp_desc with 
  | Pexp_ident {txt=Lident i; _} ->
    CValue (Var i)
  | Pexp_construct ({txt=Lident "true"; _}, None) ->
    CValue TTrue
  | Pexp_construct ({txt=Lident "false"; _}, None) ->
    CValue TFalse
  | Pexp_construct ({txt=Lident "()"; _}, None) ->
    CValue (UNIT)
  | Pexp_constant c ->
    begin match c with
    | Pconst_integer (i, _) -> CValue (Num (int_of_string i))
    | _ -> failwith (Format.asprintf "unknown kind of constant: %a" Pprintast.expression expr)
    end
  (* lambda *)
  | Pexp_fun (_, _, _, body) ->
    (* see also: Pexp_fun case below in transform_str *)
    let spec = function_spec body in
    let formals, body = collect_param_names expr in
    let e = transformation (formals @ env) body in
    CLambda (formals, spec, e)
  (* perform *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, ((_, {pexp_desc = Pexp_construct ({txt=Lident eff; _}, args); _}) :: _)) when name = "perform" ->
    begin match args with
    | Some a -> transformation env a |> maybe_var (fun v -> CPerform (eff, Some v))
    | None -> CPerform (eff, None)
    end
  (* continue *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, _k; _, e]) when name = "continue" ->
    transformation env e |> maybe_var (fun v -> CResume v)
  (* dereference *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, {pexp_desc=Pexp_ident {txt=Lident v;_}; _}]) when name = "!" ->
    CRead v
  (* ref *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, a]) when name = "ref" ->
    transformation env a |> maybe_var (fun v -> CRef v)
  (* assign *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, {pexp_desc = Pexp_ident {txt=Lident x; _}; _}; _, e]) when name = ":=" ->
    transformation env e |> maybe_var (fun v -> CWrite (x, v))
  (* transparent *)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Ldot (Lident "Sys", "opaque_identity"); _}); _}, [_, a]) ->
    (* ignore this *)
    transformation env a
  (* primitive or invocation of higher-order function passed as argument *)
  | Pexp_construct ({txt=Lident "[]"; _}, None) ->
    CValue Nil
  | Pexp_construct ({txt=Lident ("::" as name); _}, Some ({pexp_desc = Pexp_tuple args; _})) ->
    (* this is almost the same as the next case. can't be unified because the pattern has a different type *)
    let rec loop vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars)
      |  a :: args1 ->
        transformation env a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, args) when List.mem name env || List.mem name primitives ->
    (* TODO this doesn't model ocaml's right-to-left evaluation order *)
    let rec loop vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars)
      | (_, a) :: args1 ->
        transformation env a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, args) ->
    (* unknown function call, e.g. printf. translate to assert true for now *)
    (* debug ~at:2 ~title:"unknown function call" "%a" Pprintast.expression f; *)
    (* with higher-order functions, we can no longer know statically which variables are functions, so we give up on doing this and emit a function call *)
    (* CAssert (True, EmptyHeap) *)
    let rec loop vars args =
      match args with
      | [] -> CFunCall (name, List.rev vars)
      | (_, a) :: args1 ->
        transformation env a |> maybe_var (fun v -> loop (v :: vars) args1)
    in
    loop [] args
  | Pexp_sequence (a, b) ->
    CLet ("_", transformation env a, transformation env b)
  | Pexp_assert e ->
    let p, k = expr_to_formula e in
    CAssert (p, k)
  | Pexp_let (_rec, vb::_vbs, e) ->
    let var_name = string_of_pattern (vb.pvb_pat) in 
    let exprIn = vb.pvb_expr in 
    if String.equal var_name "res" then
      failwith (Format.asprintf "cannot name variable res");
    CLet (var_name, transformation env exprIn, transformation env e)
  | Pexp_ifthenelse (if_, then_, Some else_) ->
    let expr = transformation env if_ in 
    

    (match expr with 
    | CValue v -> CIfELse ((Atomic (EQ, v, TTrue)), transformation env then_, transformation env else_)
    | CFunCall (name, [a;b]) -> 
      if String.compare name "==" ==0 then 
        CIfELse ((Atomic (EQ, a, b)), transformation env then_, transformation env else_)
        
      else 
        let v = verifier_getAfreeVar "let" in
        let rest_Expr =  CIfELse ((Atomic (EQ, Var v, TTrue)), transformation env then_, transformation env else_) in 
        CLet (v, expr, rest_Expr)

        
    | _ -> 
      let v = verifier_getAfreeVar "let" in
      let rest_Expr =  CIfELse ((Atomic (EQ,Var v, TTrue)), transformation env then_, transformation env else_) in 
      CLet (v, expr, rest_Expr)
    )
      
  | Pexp_match (spec, e, cases) ->
    let norm =
      (* may be none for non-effect pattern matches *)
      cases |> List.find_map (fun c ->
        match c.pc_lhs.ppat_desc with
        | Ppat_var {txt=v; _} -> Some (v, transformation env c.pc_rhs)
        | _ -> None)
    in
    let effs =
      (* may be empty for non-effect pattern matches *)
      cases |> List.filter_map (fun c ->
        match c.pc_lhs.ppat_desc with
        | Ppat_effect (peff, _pk) ->
          let label, arg_binder =
            let arg =
              match peff with
              | {ppat_desc = Ppat_construct (_name, Some a); _} -> Some (string_of_pattern a)
              | {ppat_desc = Ppat_construct (_name, None); _} -> None
              | _ -> failwith (Format.asprintf "unknown kind of effect constructor pattern: %a" Pprintast.pattern peff)
            in
            string_of_pattern peff, arg
          in
          Some (label, arg_binder, c.pc_spec, transformation env c.pc_rhs)
        | _ -> None)
    in
    let pattern_cases =
      (* may be empty for non-effect pattern matches *)
      cases |> List.filter_map (fun c ->
        match c.pc_lhs.ppat_desc with
        | Ppat_construct ({txt=constr; _}, None) ->
          Some (Longident.last constr, [], transformation env c.pc_rhs)
        | Ppat_construct ({txt=constr; _}, Some {ppat_desc = Ppat_tuple ps; _}) ->
          let args = List.filter_map (fun p ->
            match p.ppat_desc with
            | Ppat_var {txt=v; _} -> Some v
            | _ -> None) ps
          in
          Some (Longident.last constr, args, transformation env c.pc_rhs)
        | _ -> None)
    in
    CMatch (spec (*SYHTODO*), transformation env e, norm, effs, pattern_cases)
  | _ ->
    failwith (Format.asprintf "expression not in core language: %a" Pprintast.expression expr)
    (* (Printast.expression 0) expr *)

and maybe_var f e =
  (* generate fewer unnecessary variables *)
  match e with
  | CValue v -> f v
  | _ ->
    let v = verifier_getAfreeVar "let" in
    CLet (v, e, f (Var v))

type experiemntal_data = (float list * float list) 



(* let enatilmentHeapAssertion k1 pi : bool = 
  let (re, _) = check_pure (kappaToPure k1) pi in re *)

let rec lookUpFromPure p str : term option = 
  match p with 
  | True -> None 
  | False -> None 
  | Atomic (EQ, Var name , Num i) -> 
    if String.compare str name == 0 then Some (Num i)
    else None 

  | And   (p1, p2) -> 
    (match lookUpFromPure p1 str with 
    | None -> lookUpFromPure p2 str
    | Some n -> Some n 
    )
  | Atomic _
  | Or    _
  | Imply  _
  | Not   _
  | Predicate _ -> None (*raise (Foo "lookUpFromPure error")*)








let transform_str env (s : structure_item) =
  match s.pstr_desc with
  | Pstr_value (_rec_flag, vb::_vbs_) ->
    let tactics = collect_annotations vb.pvb_attributes in
    let fn_name = string_of_pattern vb.pvb_pat in
    let fn = vb.pvb_expr in
    begin match fn.pexp_desc with
    | Pexp_fun (_, _, _, tlbody) ->
      (* see also: CLambda case *)
      let spec = function_spec tlbody in
      let formals, body = collect_param_names fn in
      let e = transformation (fn_name :: formals @ env) body in
      Some (`Meth (fn_name, formals, spec, e, tactics))
    | Pexp_apply _ -> None 
    | whatever -> 
      print_endline (string_of_expression_kind whatever); 
      failwith (Format.asprintf "not a function binding: %a" Pprintast.expression fn)
    end
    
  | Pstr_lemma (_l_name, _l_left, _l_right) ->
    failwith "parsing user-defined lemma, TODO"
  | Pstr_predicate (p_name, p_params, p_body) -> Some (`Pred {p_name; p_params; p_body})
  | Pstr_SL_predicate (p_sl_ex, p_sl_name, p_sl_params, p_sl_body) -> Some (`SLPred {p_sl_ex; p_sl_name; p_sl_params; p_sl_body})

  | Pstr_effect { peff_name; peff_kind=_; _ } ->
      let name = peff_name.txt in
      Some (`Eff name)
  | Pstr_type _ 
  | Pstr_typext _ -> None 
  | _ -> failwith (Format.asprintf "unknown program element: %a" Pprintast.structure [s])




let replaceSLPredicatesWithDefInState ((pure, heap):state) (slps:sl_pred_def SMap.t): (string list * state) = 
  
  let rec decomposePredicate p =
    match p with 
    | Predicate (str, actualArg) -> 
      (try 
      let ({p_sl_ex; p_sl_name; p_sl_params; p_sl_body}:sl_pred_def)  = SMap.find str slps in 
      assert (String.compare p_sl_name str == 0);

      let (p_sl_ex, p_sl_body) = renamingexistientalVarState p_sl_ex p_sl_body in 
      let bindings = bindFormalNActual (p_sl_params) (actualArg) in 
      let (pi, kappa) = p_sl_body in 
      let p_sl_body' = (instantiatePure bindings pi, instantiateHeap bindings kappa) in 
      let (pNew, heapNew) = p_sl_body' in 
      (p_sl_ex, (pNew, Some heapNew))
      with 
      | Not_found -> 
        raise (Failure (str ^ " not found"))

      )

      
      

    | And   (p1, p2) -> 
      let (ex1, (morePure1, moreHeap1)) = decomposePredicate p1 in 
      let (ex2, (morePure2, moreHeap2)) = decomposePredicate p2 in 
      let unionHeap = 
        match (moreHeap1, moreHeap2) with 
        | (None, None) -> None 
        | (Some h1, None) -> Some h1
        | (None, Some h2) -> Some h2
        | (Some h1, Some h2) -> Some (SepConj(h1, h2))
      in  
      (ex1@ex2, (And (morePure1, morePure2), unionHeap))


    | Atomic _
    | True 
    | False -> [], (p, None)  
    | Not _  
    | Or    _
    | Imply  _ -> failwith "decomposePredicate nor and or and imply"
  in 


  
  let (ex, (morePure, moreHeap)) = decomposePredicate pure in 
  let heap' = match moreHeap with None -> heap | Some moreH -> SepConj (heap, moreH) in 
  (ex, (morePure, heap'))





let replaceSLPredicatesWithDef (specs:disj_spec) (slps:sl_pred_def SMap.t) = 
  let rec helper (stage:normalisedStagedSpec): normalisedStagedSpec = 
    let (effS, normalS) = stage in
    match effS with
    | [] ->
      let (existiental, (p1, h1), (p2, h2)) = normalS in
      let (ex1, (p1', h1')) = replaceSLPredicatesWithDefInState (p1, h1) slps in 
      let (ex2, (p2', h2')) = replaceSLPredicatesWithDefInState (p2, h2) slps in 
      ([], (existiental@ex1@ex2, (p1', h1'), (p2', h2')))

    | x :: xs  ->
      let {e_evars; e_pre ; e_post; e_constr; e_ret; e_typ} = x in
      let (p1, h1) = e_pre in 
      let (p2, h2) = e_post in 
      let (ex1, (p1', h1')) = replaceSLPredicatesWithDefInState (p1, h1) slps in 
      let (ex2, (p2', h2')) = replaceSLPredicatesWithDefInState (p2, h2) slps in 
      let x' = {e_evars=e_evars@ex1@ex2; e_pre=(p1', h1'); e_post=(p2', h2'); e_constr=e_constr; e_ret=e_ret; e_typ=e_typ} in 

      let (xs', normal') = helper (xs, normalS) in 
      (x'::xs', normal')



  in List.map (fun spec -> 
    let (spec:normalisedStagedSpec) = normalize_spec spec in 
    let spec' = helper spec in 
    normalisedStagedSpec2Spec spec'
  ) specs
  


let replacePredicatesWithDef (specs:disj_spec) (ps:pred_def SMap.t) : disj_spec = 
  let rec helper (spec:spec) : disj_spec = 
    match spec with 
    | [] -> [[]]
    | HigherOrder (pi, h, (f, actualArg), ret) :: xs  -> 
      (try 
      (let ({p_name; p_params; p_body}:pred_def)  = SMap.find f ps in 
      assert (String.compare p_name f == 0);
      let bindings = bindFormalNActual (p_params) (actualArg@[ret]) in 

      let p_body = renamingexistientalVar p_body in 
      let p_body' =  (instantiateSpecList bindings p_body)  in 

      let temp = helper xs in 
      List.flatten (List.map (fun li -> 
        List.map (
          fun p_b -> 
            NormalReturn(pi, h) ::p_b  @ li
        ) p_body'
      ) temp))
      with 
      | Not_found -> 
        let temp = helper xs in 
        List.map (fun li -> HigherOrder (pi, h, (f, actualArg), ret) :: li) temp
      )

    | x :: xs  -> 
      let temp = helper xs in 
      List.map (fun li -> x :: li) temp



  
  in  List.flatten (List.map (fun spec -> helper spec) specs)


let transform_strs (strs: structure_item list) : core_program =
  let _env, effs, mths, preds, sl_preds, lems =
    List.fold_left (fun (env, es, ms, ps, slps, ls) c ->
      match transform_str env c with
      | Some (`Lem l) -> env, es, ms, ps, slps, SMap.add l.p_name l ls
      | Some (`Pred p) -> 
        print_endline ("\n"^ p.p_name ^ ":");
        print_endline (string_of_disj_spec p.p_body);

        let body' = replaceSLPredicatesWithDef p.p_body slps in 
        print_endline ("~~~> " ^ string_of_disj_spec body');

        let (p': pred_def) = {p_name =p.p_name; p_params = p.p_params; p_body = body'} in 
        env, es, ms, SMap.add p'.p_name p' ps, slps, ls

      | Some (`SLPred p) -> env, es, ms, ps, SMap.add p.p_sl_name p slps,ls
      | Some (`Eff a) -> env, a :: es, ms, ps, slps, ls
      | Some (`Meth (m_name, m_params, m_spec, m_body, m_tactics)) -> 
        let m_spec' = 
          (match m_spec with 
          | None -> None 
          | Some spec -> 
          print_endline ("\n"^ m_name ^ ":");
          print_endline (string_of_disj_spec spec);
          let spec' = replacePredicatesWithDef spec ps in 
          print_endline ("~~~> " ^ string_of_disj_spec spec');
          let spec'' = replaceSLPredicatesWithDef spec' slps in 
          print_endline ("~~~> " ^ string_of_disj_spec spec'');
          Some spec''
          ) 
        in 
        m_name :: env, es, { m_name=m_name; m_params=m_params; m_spec=m_spec'; m_body=m_body; m_tactics=m_tactics } :: ms, ps, slps, ls
      | _ -> env, es, ms, ps, slps, ls
    ) ([], [], [], SMap.empty, SMap.empty, SMap.empty) strs
  in { cp_effs = List.rev effs; cp_methods = List.rev mths; cp_predicates = preds; cp_sl_predicates = sl_preds; cp_lemmas = lems }

let string_of_token =
  let open Parser in
  function
| AMPERAMPER -> "AMPERAMPER"
| AMPERSAND -> "AMPERSAND"
| AND -> "AND"
| AS -> "AS"
| ASSERT -> "ASSERT"
| BACKQUOTE -> "BACKQUOTE"
| BANG -> "BANG"
| BAR -> "BAR"
| BARBAR -> "BARBAR"
| BARRBRACKET -> "BARRBRACKET"
| BEGIN -> "BEGIN"
| CHAR _ -> "CHAR"
| CLASS -> "CLASS"
| COLON -> "COLON"
| COLONCOLON -> "COLONCOLON"
| COLONEQUAL -> "COLONEQUAL"
| COLONGREATER -> "COLONGREATER"
| COMMA -> "COMMA"
| CONSTRAINT -> "CONSTRAINT"
| DO -> "DO"
| DONE -> "DONE"
| DOT -> "DOT"
| DOTDOT -> "DOTDOT"
| DOWNTO -> "DOWNTO"
| EFFECT -> "EFFECT"
| EXISTS -> "EXISTS"
| ELSE -> "ELSE"
| END -> "END"
| EOF -> "EOF"
| EQUAL -> "EQUAL"
| EXCEPTION -> "EXCEPTION"
| EXTERNAL -> "EXTERNAL"
| FALSE -> "FALSE"
| FLOAT _ -> "FLOAT"
| FOR -> "FOR"
| FUN -> "FUN"
| FUNCTION -> "FUNCTION"
| FUNCTOR -> "FUNCTOR"
| REQUIRES -> "REQUIRES"
| ENSURES -> "ENSURES"
| EMP -> "EMP"
| GREATER -> "GREATER"
| GREATERRBRACE -> "GREATERRBRACE"
| GREATERRBRACKET -> "GREATERRBRACKET"
| IF -> "IF"
| IN -> "IN"
| INCLUDE -> "INCLUDE"
| INFIXOP0 _ -> "INFIXOP0"
| INFIXOP1 _ -> "INFIXOP1"
| INFIXOP2 _ -> "INFIXOP2"
| INFIXOP3 _ -> "INFIXOP3"
| INFIXOP4 _ -> "INFIXOP4"
| DOTOP _ -> "DOTOP"
| LETOP _ -> "LETOP"
| ANDOP _ -> "ANDOP"
| INHERIT -> "INHERIT"
| INITIALIZER -> "INITIALIZER"
| INT _ -> "INT"
| LABEL _ -> "LABEL"
| LAZY -> "LAZY"
| LBRACE -> "LBRACE"
| LBRACELESS -> "LBRACELESS"
| LBRACKET -> "LBRACKET"
| LBRACKETBAR -> "LBRACKETBAR"
| LBRACKETLESS -> "LBRACKETLESS"
| LBRACKETGREATER -> "LBRACKETGREATER"
| LBRACKETPERCENT -> "LBRACKETPERCENT"
| LBRACKETPERCENTPERCENT -> "LBRACKETPERCENTPERCENT"
| LESS -> "LESS"
| LESSMINUS -> "LESSMINUS"
| LET -> "LET"
| LIDENT _ -> "LIDENT"
| LPAREN -> "LPAREN"
| LBRACKETAT -> "LBRACKETAT"
| LBRACKETATAT -> "LBRACKETATAT"
| LBRACKETATATAT -> "LBRACKETATATAT"
| MATCH -> "MATCH"
| METHOD -> "METHOD"
| MINUS -> "MINUS"
| MINUSDOT -> "MINUSDOT"
| MINUSGREATER -> "MINUSGREATER"
| MODULE -> "MODULE"
| MUTABLE -> "MUTABLE"
| NEW -> "NEW"
| NONREC -> "NONREC"
| OBJECT -> "OBJECT"
| OF -> "OF"
| OPEN -> "OPEN"
| OPTLABEL _ -> "OPTLABEL"
| OR -> "OR"
| PERCENT -> "PERCENT"
| PLUS -> "PLUS"
| PLUSDOT -> "PLUSDOT"
| PLUSEQ -> "PLUSEQ"
| PREFIXOP _ -> "PREFIXOP"
| PRIVATE -> "PRIVATE"
| QUESTION -> "QUESTION"
| QUOTE -> "QUOTE"
| RBRACE -> "RBRACE"
| RBRACKET -> "RBRACKET"
| REC -> "REC"
| RPAREN -> "RPAREN"
| SEMI -> "SEMI"
| SEMISEMI -> "SEMISEMI"
| HASH -> "HASH"
| HASHOP _ -> "HASHOP"
| SIG -> "SIG"
| STAR -> "STAR"
| STRING _ -> "STRING"
| STRUCT -> "STRUCT"
| THEN -> "THEN"
| TILDE -> "TILDE"
| TO -> "TO"
| TRUE -> "TRUE"
| TRY -> "TRY"
| TYPE -> "TYPE"
| UIDENT _ -> "UIDENT"
| UNDERSCORE -> "UNDERSCORE"
| VAL -> "VAL"
| VIRTUAL -> "VIRTUAL"
| WHEN -> "WHEN"
| WHILE -> "WHILE"
| WITH -> "WITH"
| COMMENT _ -> "COMMENT"
| LSPECCOMMENT -> "LSPECCOMMENT"
| RSPECCOMMENT -> "RSPECCOMMENT"
| PREDICATE -> "PREDICATE"
| LEMMA -> "LEMMA"
| DOCSTRING _ -> "DOCSTRING"
| EOL -> "EOL"
| QUOTED_STRING_EXPR _ -> "QUOTED_STRING_EXPR"
| QUOTED_STRING_ITEM _ -> "QUOTED_STRING_ITEM"
| CONJUNCTION -> "CONJUNCTION"
| DISJUNCTION -> "DISJUNCTION"
| IMPLICATION -> "IMPLICATION"


let debug_tokens str =
  let lb = Lexing.from_string str in
  let rec loop tokens =
    let tok = Lexer.token lb in
    match tok with
    | EOF -> List.rev (tok :: tokens)
    | _ -> loop (tok :: tokens)
  in
  let tokens = loop [] in
  let s = tokens |> List.map string_of_token |> String.concat " " in
  Format.printf "%s@." s

let (exGlobal:(string list) ref) =  ref []
let (unifyGlobal: pi ref) = ref True  

let term_is_Extiatential t ctx =
  match t with 
  | Var str -> if existStr str ctx then true else false 
  | _ -> false 

let normaliseKappa k = 
  match k with 
  | SepConj ( sp1, EmptyHeap) -> sp1 
  | SepConj ( EmptyHeap, sp2) -> sp2  
  | _ -> k 

let rec speration_logic_ential (p1, h1) (p2, h2) : (bool) = 
(*print_endline (string_of_state (p1, h1) ^" ==> "^  string_of_state (p2, h2)); *)
let h1 = normaliseKappa h1 in 
let h2 = normaliseKappa h2 in 
let res = 
  match (h1, h2) with 
  | (_, EmptyHeap) -> true
  | (EmptyHeap, _) -> false
  | (PointsTo (v1, t1), PointsTo (v2, t2)) -> 
    if existStr v2 !exGlobal && stricTcompareTerm t1 t2 then 
      let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, Var v1, Var v2), p1)) in 
      (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, Var v1, Var v2), p1)) ^ "\n");*)
      true
    else if existStr v2 !exGlobal then 
      if term_is_Extiatential t2 !exGlobal then 
        let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, t1, t2), p1)) in 
        (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, t1, t2), p1)) ^ "\n");*)
        true
      else 
      let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, Var v1, Var v2), p1)) in 
      (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, Var v1, Var v2), p1)) ^ "\n");*)
      let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
      let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
      (*print_endline ( "yoyo1\n");
      print_endline (string_of_pi (!unifyGlobal));*)
      (ProversEx.entailConstrains (And(lhs, !unifyGlobal)) rhs)

    else 
      (match (t2) with 
      | Var t2Str -> 
        if existStr t2Str !exGlobal then 
          let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, t1, t2), p1)) in 
          (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, t1, t2), p1)) ^ "\n");*)
          true
        else 
          let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
          let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
          (ProversEx.entailConstrains (And(lhs, !unifyGlobal)) rhs)
      | _ -> 
      let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
      let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
      (ProversEx.entailConstrains (And(lhs, !unifyGlobal)) rhs))

  | (SepConj ( sp1, sp2), SepConj ( sp3, sp4)) -> 
    speration_logic_ential (p1, sp1) (p2, sp3) && speration_logic_ential (p1, sp2) (p2, sp4)
      
  | _ -> failwith ("not supporting other heap")
in (*print_string (string_of_bool res ^ "\n\n");*) res



let checkEntailmentForNormalFlow (lhs:normalStage) (rhs:normalStage) : bool = 
  let (ex1, (pi1, heap1), (pi2, heap2)) = lhs in 
  let (ex2, (pi3, heap3), (pi4, heap4)) = rhs in  
  let () = exGlobal := !exGlobal @ ex1 @ ex2 in 
  let (contravariant) = speration_logic_ential (pi3, heap3) (pi1, heap1) in 
  let (covariant)     = speration_logic_ential (pi2, heap2) (pi4, heap4) in 
  covariant && contravariant


let rec compareEffectArgument unification v1 v2 =  
  match (v1, v2) with 
  | ([], []) -> true 
  | (x::xs, y::ys) -> 
    let r1 = ProversEx.entailConstrains unification (Atomic(EQ, x, y)) in 
    r1 && (compareEffectArgument unification xs ys)
  | (_, _) -> false 

let checkEntailMentForEffFlow (lhs:effectStage) (rhs:effectStage) : (bool) = 
  let {e_evars=ex1; e_pre=(pi1, heap1); e_post=(pi2, heap2); e_constr=(eff1, v1); e_ret=r1; _} = lhs in 
  let {e_evars=ex2; e_pre=(pi3, heap3); e_post=(pi4, heap4); e_constr=(eff2, v2); e_ret=r2; _} = rhs in  
  let () = exGlobal := !exGlobal @ ex1 @ ex2 in 
  let (contravariant) = speration_logic_ential (pi3, heap3) (pi1, heap1) in 
  let (covariant)     = speration_logic_ential (pi2, heap2) (pi4, heap4) in 
  let effectName    = String.compare eff1 eff2 == 0  in 
  let effArgument   = compareEffectArgument !unifyGlobal v1 v2 in 
  let () =  unifyGlobal := And (!unifyGlobal, (Atomic(EQ, r1, r2))) in 
  (covariant && contravariant && effectName && effArgument) 

let rec entailmentchecking_aux (lhs:normalisedStagedSpec) (rhs:normalisedStagedSpec) : (bool) = 
  (*print_endline (string_of_pi (!unifyGlobal));
  print_endline (string_of_normalisedStagedSpec lhs ^" |===> "^ string_of_normalisedStagedSpec rhs);
  *)
  let (effSLHS, normalSLHS)  =  lhs  in 
  let (effSRHS, normalSRHS)  =  rhs  in 
  match (effSLHS, effSRHS) with 
  | ([], []) -> checkEntailmentForNormalFlow normalSLHS normalSRHS 
  | (x::xs, y::ys) -> 
    let (r1) = checkEntailMentForEffFlow x y in 
    let r2 = entailmentchecking_aux (xs, normalSLHS) (ys, normalSRHS) in 
    r1 && r2
  | (_, _) -> false 


let rec entailmentchecking_helper (lhs:normalisedStagedSpec) (rhs:normalisedStagedSpec list) : (bool) =
  match rhs with 
  | [] -> false 
  | y::ys -> 

    let () = exGlobal := [] in 
    let () = unifyGlobal := True in 

    let r1 = entailmentchecking_aux lhs y in 
    
    let r2 = entailmentchecking_helper lhs ys in 
    r1 || r2


let rec entailmentchecking (lhs:normalisedStagedSpec list) (rhs:normalisedStagedSpec list) : (bool) = 
  match (lhs) with 
  | [] -> true 
  | x :: xs -> 
    let r1 = entailmentchecking_helper x rhs in 
    let r2 = entailmentchecking xs rhs in 
    r1 && r2

let normal_report ?(kind="Function") ?given_spec ?given_spec_n ?inferred_spec ?inferred_spec_n ?forward_time_ms ?entail_time_ms ?result name =
  let header =
    "\n========== " ^ kind ^ ": "^ name ^" ==========\n" ^
    (match given_spec with
    | Some s -> "[Specification] " ^ string_of_spec_list s ^ "\n"
    | None -> "") ^
    (match given_spec_n with
    | Some s -> "[Normed   Spec] " ^ string_of_spec_list (normalise_spec_list_aux2 s) ^ "\n"
    | None -> "") ^
    (match inferred_spec with
    | Some s -> "[Raw Post Spec] " ^ string_of_spec_list s ^ "\n"
    | None -> "") ^
    (match inferred_spec_n with
    | Some s -> 
    
        (*print_endline ("\ninferred_spec_n:");
        let _ = List.iter (fun spec -> print_endline (string_of_normalisedStagedSpec spec) ) s in 
        print_endline("\n----------------");

        print_endline (string_of_spec_list (normalise_spec_list_aux2 s)); 
*)
      "[Normed   Post] " ^ string_of_spec_list (normalise_spec_list (normalise_spec_list_aux2 s)) ^ "\n"
    | None -> "") ^
    (match forward_time_ms with
    | Some t -> "[Forward  Time] " ^ string_of_time t ^ " ms\n"
    | None -> "") ^
    (match result with
    | Some r ->
      let don't_worry = if not r && String.ends_with ~suffix:"_false" name then " (expected)" else "" in 
      "[Entail  Check] " ^ (string_of_res r) ^ don't_worry ^ "\n"
    | None -> "") ^
    (match entail_time_ms with
    | Some t -> "[Entail   Time] " ^ string_of_time t ^ " ms\n"
    | None -> "") ^
    ("[Z3       Time] " ^ string_of_time !z3_consumption^ " ms\n")
    
    ^
    (String.init (String.length name + 32) (fun _ -> '=')) ^ "\n"
  in
  Format.printf "%s@." header

let test_report ?kind:_ ?given_spec:_ ?given_spec_n:_ ?inferred_spec:_ ?inferred_spec_n:_ ?forward_time_ms:_ ?entail_time_ms:_ ?result name =
  let false_expected = String.ends_with ~suffix:"_false" name in
  match result with
  | Some true when false_expected ->
    tests_failed := true;
    Format.printf "FAILED: %s@." name
  | Some false when not false_expected ->
    tests_failed := true;
    Format.printf "FAILED: %s@." name
  | _ -> ()

let report_result ?kind ?given_spec ?given_spec_n ?inferred_spec ?inferred_spec_n ?forward_time_ms ?entail_time_ms ?result name =
  let f =
    if !test_mode then test_report else normal_report
  in
  f ?kind ?given_spec ?given_spec_n ?inferred_spec ?inferred_spec_n ?forward_time_ms ?entail_time_ms ?result name

let check_obligation meth prog predicates (l, r) =
  let res = Entail.check_staged_subsumption_disj meth.m_name meth.m_params meth.m_tactics prog.cp_lemmas predicates l r in
  report_result ~kind:"Obligation" ~given_spec:r ~inferred_spec:l ~result:res meth.m_name

exception Method_failure

let analyze_method prog ({m_spec = given_spec; _} as meth) =
  let () =  z3_consumption := 0.0 in 
  let time_stamp_beforeForward = Sys.time () in
  let inferred_spec, predicates, fvenv =
    (* the env is looked up from the program every time, as it's updated as we go *)
    let method_env = prog.cp_methods
      (* within a method body, params/locals should shadow functions defined outside *)
      |> List.filter (fun m -> not (List.mem m.m_name meth.m_params))
      (* treat recursive calls as abstract, as recursive functions should be summarized using predicates *)
      |> List.filter (fun m -> not (String.equal m.m_name meth.m_name))
      |> List.map (fun m -> m.m_name, m)
      |> List.to_seq
      |> SMap.of_seq
    in
    let env = create_fv_env method_env in
    let inf, env = infer_of_expression env [freshNormalReturnSpec] meth.m_body in

    (* make the new specs inferred for lambdas available to the entailment procedure as predicates *)
    let preds_with_lambdas =
      let lambda =
        env.fv_methods
        |> SMap.filter (fun k _ -> not (SMap.mem k method_env))
        |> SMap.map (fun meth -> Entail.derive_predicate meth.m_name meth.m_params (Option.get meth.m_spec)) (* these have to have specs as they did not occur earlier, indicating they are lambdask *)
        |> SMap.to_seq
      in
      SMap.add_seq lambda prog.cp_predicates
    in
    inf, preds_with_lambdas, env
  in
  (* check misc obligations. don't stop on failure for now *)
  fvenv.fv_lambda_obl |> List.iter (check_obligation meth prog predicates);
  fvenv.fv_match_obl |> List.iter (check_obligation meth prog predicates);

  (* check the main spec *)
  let time_stamp_afterForward = Sys.time () in

  (*print_endline ("\n----------------\ninferred_spec: \n" ^ string_of_spec_list inferred_spec);*)

  let inferred_spec_n = 
  try
      
      normalise_spec_list_aux1 inferred_spec
    with Norm_failure -> report_result ~inferred_spec ~result:false meth.m_name; raise Method_failure
  
  in



  let res =
    match given_spec with
    | Some given_spec ->
      let given_spec_n =
        try
          normalise_spec_list_aux1 given_spec
        with Norm_failure -> report_result ~inferred_spec ~inferred_spec_n ~given_spec ~result:false meth.m_name; raise Method_failure
      in
      let time_stamp_afterNormal = Sys.time () in
      let res =
        try
          let syh_old_entailment = false in
          match syh_old_entailment with
          | true -> entailmentchecking inferred_spec_n given_spec_n
          | false ->
            (* normalization occurs after unfolding in entailment *)

            (*print_endline ("proving!!!==================================") ;
            print_endline ("inferred_spec_n " ^ string_of_normalisedStagedSpecList inferred_spec_n);
            print_endline (" |= ") ;
            print_endline ("given_spec_n " ^ string_of_normalisedStagedSpecList given_spec_n);
*)
            let res = Entail.check_staged_subsumption_disj meth.m_name meth.m_params meth.m_tactics prog.cp_lemmas predicates inferred_spec given_spec in 
            (*print_endline ("proving end!!!==================================") ;
            *)
            res

        with Norm_failure ->
          (* norm failing all the way to the top level may prevent some branches from being explored during proof search. this does not happen in any tests yet, however, so keep error-handling simple. if it ever happens, return an option from norm entry points *)
          false
      in
      let time_stamp_afterEntail = Sys.time () in
      let entail_time_ms = ((time_stamp_afterEntail -. time_stamp_afterNormal) *. 1000.0) in
      let forward_time_ms = ((time_stamp_afterForward -. time_stamp_beforeForward) *. 1000.0) in
      report_result ~inferred_spec ~inferred_spec_n ~given_spec ~given_spec_n ~entail_time_ms ~forward_time_ms ~result:res meth.m_name;
      res
    | None ->
      report_result ~inferred_spec ~inferred_spec_n meth.m_name;
      true
  in
  (* only save these specs for use by later functions if verification succeeds *)
  if not res then prog else (
    let prog, pred =
      (* if the user has not provided a predicate for the given function,
        produce one from the inferred spec *)
      let p = Entail.derive_predicate meth.m_name meth.m_params inferred_spec in
      let cp_predicates = SMap.update meth.m_name
        (function
        | None ->
          info ~title:(Format.asprintf "remembering predicate for %s" meth.m_name) "%s" (string_of_pred p);
          Some p
        | Some _ -> None) prog.cp_predicates
      in
      { prog with cp_predicates }, p
    in
    let prog =
      (* if the user has not provided a spec for the given function, remember the inferred method spec for future use *)
      match given_spec with
      | None ->
        (* using the predicate instead of the raw inferred spec makes the induction hypothesis possible with current heuristics. it costs one more unfold but that is taken care of by the current entailment procedure, which repeatedly unfolds *)
        let _mspec : disj_spec = inferred_spec in
        let mspec : disj_spec =
          let v = verifier_getAfreeVar "infr" in
          let prr, _ret = split_last pred.p_params in
          let sp = [Exists [v]; HigherOrder (True, EmptyHeap, (pred.p_name, List.map (fun v1 -> Var v1) prr), Var v)]
          in
          [sp]
        in
        info ~title:(Format.asprintf "inferred spec for %s" meth.m_name) "%s" (string_of_disj_spec mspec);
        let cp_methods = List.map (fun m -> if String.equal m.m_name meth.m_name then { m with m_spec = Some mspec } else m ) prog.cp_methods
        in
        { prog with cp_methods }
      | Some _ -> prog
    in
    prog)

let run_string_ line =
  let progs = Parser.implementation Lexer.token (Lexing.from_string line) in
  let prog = transform_strs progs in
  debug ~at:2 ~title:"parsed" "%s" (string_of_program prog);
  debug ~at:2 ~title:"user-specified predicates" "%s" (string_of_smap string_of_pred prog.cp_predicates);
  (* as we handle methods, predicates are inferred and are used in place of absent specifications, so we have to keep updating the program as we go *)
  List.fold_left (fun prog meth ->
    info ~title:(Format.asprintf "verifying: %s" meth.m_name) "";
    try
      analyze_method prog meth
    with Method_failure -> prog) prog prog.cp_methods |> ignore

let run_string s =
  Provers.handle (fun () -> run_string_ s)

let run_file inputfile =
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      
      (* debug_tokens line; *)

      run_string line;


      (* let results, _ =
        List.fold_left (fun (s, env) a ->
          let spec, env1 = infer_of_program env a in
          spec :: s, env1
        ) ([], Env.empty) progs
      in *)
 
      (* print_endline (results |> List.rev |> String.concat ""); *)



      (* 
      print_endline (testSleek ());

      *)
      (*print_endline (Pprintast.string_of_structure progs ) ; *)
      
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

let main () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
  run_file inputfile;
  if !test_mode && not !tests_failed then Format.printf "ALL OK!@."