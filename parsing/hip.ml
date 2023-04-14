

exception Foo of string
open Parsetree
open Asttypes
(* get rid of the alias *)
type string = label
open Rewriting
open Pretty
open Types

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

let string_of_program ((_es, ms):core_program) :string =
  List.map (fun (name, args, spec, body) ->
    Format.asprintf "let rec %s %s\n(*@@ %s @@*)\n=\n%s" name
    (match args with | [] -> "()" | _ -> String.concat " " args)
    (List.map string_of_spec spec |> String.concat "\n\\/\n")
    (string_of_core_lang body)
  ) ms |> String.concat "\n\n"


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

module SMap = Map.Make (struct
  type t = string
  let compare = compare
end)

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

let rec retriveFuntionWithoutSpecDefinition str li = 
  match li with 
  | [] ->  None 
  | (s, b, f) :: xs  -> if String.compare s str == 0 then (Some (s, b, f)) 
  else retriveFuntionWithoutSpecDefinition str xs 


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



let rec string_of_list (li: 'a list ) (f : 'a -> 'b) : string = 
  match li with 
  | [] -> ""
  | x::xs-> f x ^ "," ^ string_of_list xs f ;;




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

let expr_to_formula (expr:expression) : pi * kappa =
  match expr.pexp_desc with
  | Pexp_apply ({pexp_desc = Pexp_ident {txt=Lident i; _}; _}, [(_, a); (_, b)]) ->
      begin match i with
      | "=" ->
        begin match a.pexp_desc, b.pexp_desc with
        | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident "!"; _}); _}, [_, {pexp_desc = Pexp_ident {txt=Lident p; _}; _}]), _ ->
          True, PointsTo (p, expr_to_term b)
        | _ ->
          failwith (Format.asprintf "unknown kind of equality: %a" Pprintast.expression expr)
        end
      | "<" -> Atomic (LT, expr_to_term a, expr_to_term b), EmptyHeap
      | "<=" -> Atomic (LTEQ, expr_to_term a, expr_to_term b), EmptyHeap
      | ">" -> Atomic (GT, expr_to_term a, expr_to_term b), EmptyHeap
      | ">=" -> Atomic (GTEQ, expr_to_term a, expr_to_term b), EmptyHeap
        (* TODO handle heap *)
      (* | "&&" -> And (expr_to_formula a, expr_to_formula b), EmptyHeap *)
      (* | "||" -> Or (expr_to_formula a, expr_to_formula b), EmptyHeap *)
      (* | "=>" -> Imply (expr_to_formula a, expr_to_formula b), EmptyHeap *)
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


let primitives = ["+"; "-"]

(** the env just tracks the names of bound functions *)
let rec transformation (env:string list) (expr:expression) : core_lang =
  match expr.pexp_desc with 
  | Pexp_ident {txt=Lident i; _} ->
    CValue (Var i)
  | Pexp_construct ({txt=Lident "()"; _}, None) ->
    CValue (UNIT)
  | Pexp_constant c ->
    begin match c with
    | Pconst_integer (i, _) -> CValue (Num (int_of_string i))
    | _ -> failwith (Format.asprintf "unknown kind of constant: %a" Pprintast.expression expr)
    end
  | Pexp_fun _ ->
    failwith (Format.asprintf "only for higher-order, TBD: %a" Pprintast.expression expr)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, ((_, {pexp_desc = Pexp_construct ({txt=Lident eff; _}, args); _}) :: _)) when name = "perform" ->
    begin match args with
    | Some a -> transformation env a |> maybe_var (fun v -> CPerform (eff, Some v))
    | None -> CPerform (eff, None)
    end
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, _k; _, e]) when name = "continue" ->
    transformation env e |> maybe_var (fun v -> CResume v)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, {pexp_desc=Pexp_ident {txt=Lident v;_}; _}]) when name = "!" ->
    CRead v
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, a]) when name = "ref" ->
    transformation env a |> maybe_var (fun v -> CRef v)
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, [_, {pexp_desc = Pexp_ident {txt=Lident x; _}; _}; _, e]) when name = ":=" ->
    transformation env e |> maybe_var (fun v -> CWrite (x, v))
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Ldot (Lident "Sys", "opaque_identity"); _}); _}, [_, a]) ->
    (* ignore this *)
    transformation env a
  | Pexp_apply ({pexp_desc = Pexp_ident ({txt = Lident name; _}); _}, args) when List.mem name env || List.mem name primitives ->
    let rec loop args vars =
      match List.rev args with
      | [] -> CFunCall (name, vars)
      | (_, a) :: args1 ->
        transformation env a |> maybe_var (fun v -> loop args1 (v :: vars))
    in
    loop args []
  | Pexp_apply (_f, _args) ->
    (* unknown function call, e.g. printf. translate to assert true for now *)
    CAssert (True, EmptyHeap)
  | Pexp_sequence (a, b) ->
    CLet ("_", transformation env a, transformation env b)
  | Pexp_assert e ->
    let p, k = expr_to_formula e in
    CAssert (p, k)
  | Pexp_let (_rec, vb::_vbs, e) ->
    let var_name = string_of_pattern (vb.pvb_pat) in 
    let exprIn = vb.pvb_expr in 
    CLet (var_name, transformation env exprIn, transformation env e)
  | Pexp_ifthenelse (if_, then_, Some else_) ->
    transformation env if_
      |> maybe_var (fun v -> CIfELse (v, transformation env then_, transformation env else_))
  | Pexp_match (e, cases) ->
    let norm =
      match cases |> List.filter_map (fun c ->
        match c.pc_lhs.ppat_desc with
        | Ppat_var {txt=v; _} -> Some (v, transformation env c.pc_rhs)
        | _ -> None
      ) with
      | [] -> failwith (Format.asprintf "no value case: %a" Pprintast.expression expr)
      | c :: _ -> c
    in
    let effs =
      match cases |> List.filter_map (fun c ->
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
          Some (label, arg_binder, transformation env c.pc_rhs)
        | _ -> None
      ) with
      | [] -> failwith (Format.asprintf "no effect case: %a" Pprintast.expression expr)
      | c -> c
    in
    CMatch (transformation env e, norm, effs)
  | _ ->
    failwith (Format.asprintf "expression not in core language: %a" Pprintast.expression expr)

and maybe_var f e =
  (* generate fewer unnecessary variables *)
  match e with
  | CValue v -> f v
  | _ ->
    let v = verifier_getAfreeVar () in
    CLet (v, e, f (Var v))
      


type experiemntal_data = (float list * float list) 



let enatilmentHeapAssertion k1 pi : bool = 
  let (re, _) = check_pure (kappaToPure k1) pi in re

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
            [verifier_getAfreeVar ()]
            (* we don't currently recurse inside patterns to pull out variables, so something like
              let f () (Foo a) = 1
              will be treated as if it has no formal params. *)
        in
        let ns, body = traverse_to_body body in
        name @ ns, body
      | _ -> ([], e)
    in
    traverse_to_body rhs

let transform_str env (s : structure_item) =
  match s.pstr_desc with
  | Pstr_value (_rec_flag, vb::_vbs_) ->
    let fn_name = string_of_pattern vb.pvb_pat in
    let fn = vb.pvb_expr in
    begin match fn.pexp_desc with
    | Pexp_fun (_, _, _, tlbody) ->
      let spec =
        match function_spec tlbody with
        | None -> [] 
        | Some spec -> [spec]
      in
      let formals, body = collect_param_names fn in
      let e = transformation env body in
      `Meth (fn_name, formals, spec, e)
    | _ ->
      failwith (Format.asprintf "not a function binding: %a" Pprintast.expression fn)
    end

  (* let final =  (infer_of_expression env [[NormalReturn (True, EmptyHeap,  UNIT)]] (transformation body)) in *)

  (* let env1 = Env.add_fn fn_name { pre=spec; post=[]; formals } env in *)

  (* Some (spec, [], ( final), env1, fn_name) *)
    (* infer_of_value_binding rec_flag env x *)
(* end *)

(* meth_def = string * (string list) * (spec list) * core_lang *)
    
  | Pstr_effect { peff_name; peff_kind=_; _ } ->
      let name = peff_name.txt in
      `Eff name
    (* begin match peff_kind with
    | Peff_decl (args, res) ->
      (* converts a type of the form a -> b -> c into ([a, b], c) *)
      let split_params_fn t =
        let rec loop acc t =
          match t.ptyp_desc with
          | Ptyp_arrow (_, a, b) ->
            (* note that we don't recurse in a *)
            loop (a :: acc) b
          | Ptyp_constr ({txt=Lident "int"; _}, [])
          | Ptyp_constr ({txt=Lident "string"; _}, []) 
          | Ptyp_constr ({txt=Lident "unit"; _}, []) -> List.rev acc, t
          | _ -> failwith ("split_params_fn: " ^ debug_string_of_core_type t)
        in loop [] t
      in
      let params = List.map core_type_to_typ args in
      let res = split_params_fn res
        |> (fun (a, b) -> (List.map core_type_to_typ a, core_type_to_typ b)) in
      let def = { params; res } in
      "", Env.add_effect name def env
    | Peff_rebind _ -> failwith "unsupported effect spec rebind"
    end *)
  | _ -> failwith (Format.asprintf "unknown program element: %a" Pprintast.structure [s])

let transform_strs (strs: structure_item list) : core_program =
  let _env, effs, mths =
    List.fold_left (fun (env, es, ms) c ->
      match transform_str env c with
      | `Eff a -> env, a :: es, ms
      | `Meth ((name, _, _, _) as a) -> name :: env, es, a :: ms) ([], [], []) strs
  in List.rev effs, List.rev mths

(* returns the inference result as a string to be printed *)
(* let rec infer_of_program env x: string * env =
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
          | Ptyp_constr ({txt=Lident "string"; _}, []) 
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
  | _ -> failwith "TBD program"
  ;; *)


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

let (exGlobal:(string list) ref) =  ref []
let (unifyGlobal: pi ref) = ref True  


let speration_logic_ential (p1, h1) (p2, h2) : (bool) = 
print_endline (string_of_state (p1, h1) ^" ==> "^  string_of_state (p2, h2));
let res = 
  match (h1, h2) with 
  | (_, EmptyHeap) -> true
  | (EmptyHeap, _) -> false
  | (PointsTo (v1, t1), PointsTo (v2, t2)) -> 
    if existStr v2 !exGlobal && stricTcompareTerm t1 t2 then 
      let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, Var v1, Var v2), p1)) in 
      print_string ("adding " ^ string_of_pi (And (Atomic(EQ, Var v1, Var v2), p1)) ^ "\n");
      true
    else if existStr v2 !exGlobal then 
      let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, Var v1, Var v2), p1)) in 
      print_string ("adding " ^ string_of_pi (And (Atomic(EQ, Var v1, Var v2), p1)) ^ "\n");
      let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
      let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
      print_endline ( "yoyo1\n");
      print_endline (string_of_pi (!unifyGlobal));
      (entailConstrains (And(lhs, !unifyGlobal)) rhs)

    else 
      (match (t2) with 
      | Var t2Str -> 
        if existStr t2Str !exGlobal then 
          let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, t1, t2), p1)) in 
          print_string ("adding " ^ string_of_pi (And (Atomic(EQ, t1, t2), p1)) ^ "\n");
          true
        else 
          let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
          let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
          (entailConstrains (And(lhs, !unifyGlobal)) rhs)
      | _ -> 
      let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
      let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
      (entailConstrains (And(lhs, !unifyGlobal)) rhs))
      
  | _ -> failwith ("not supporting other heap")
in print_string (string_of_bool res ^ "\n\n"); res



let checkEntialmentForNormalFlow (lhs:normalStage) (rhs:normalStage) : bool = 
  let (ex1, (pi1, heap1), (pi2, heap2), r1) = lhs in 
  let (ex2, (pi3, heap3), (pi4, heap4), r2) = rhs in  
  let () = exGlobal := !exGlobal @ ex1 @ ex2 in 
  let (contravariant) = speration_logic_ential (pi3, heap3) (pi1, heap1) in 
  let (covariant)     = speration_logic_ential (pi2, heap2) (pi4, heap4) in 
  let returnValue   = entailConstrains !unifyGlobal (Atomic(EQ, r1, r2)) in 
  covariant && contravariant && returnValue


let rec compareEffectArgument unification v1 v2 =  
  match (v1, v2) with 
  | ([], []) -> true 
  | (x::xs, y::ys) -> 
    let r1 = entailConstrains unification (Atomic(EQ, x, y)) in 
    r1 && (compareEffectArgument unification xs ys)
  | (_, _) -> false 

let checkEntialMentForEffFlow (lhs:effectStage) (rhs:effectStage) : (bool) = 
  let (ex1, (pi1, heap1), (pi2, heap2), (eff1, v1), r1) = lhs in 
  let (ex2, (pi3, heap3), (pi4, heap4), (eff2, v2), r2) = rhs in  
  let () = exGlobal := !exGlobal @ ex1 @ ex2 in 
  let (contravariant) = speration_logic_ential (pi3, heap3) (pi1, heap1) in 
  let (covariant)     = speration_logic_ential (pi2, heap2) (pi4, heap4) in 
  let effectName    = String.compare eff1 eff2 == 0  in 
  let effArgument   = compareEffectArgument !unifyGlobal v1 v2 in 
  let () =  unifyGlobal := And (!unifyGlobal, (Atomic(EQ, r1, r2))) in 
  (covariant && contravariant && effectName && effArgument) 

let rec entailmentchecking_aux (lhs:normalisedStagedSpec) (rhs:normalisedStagedSpec) : (bool) = 
  print_endline (string_of_normalisedStagedSpec lhs ^" |===> "^ string_of_normalisedStagedSpec rhs);
  
  let (effSLHS, normalSLHS)  =  lhs  in 
  let (effSRHS, normalSRHS)  =  rhs  in 
  match (effSLHS, effSRHS) with 
  | ([], []) -> checkEntialmentForNormalFlow normalSLHS normalSRHS 
  | (x::xs, y::ys) -> 
    let (r1) = checkEntialMentForEffFlow x y in 
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

      
      let _effs, methods = transform_strs progs in

      (*print_endline (string_of_program (_effs, methods));*)

      let incremental = Array.length Sys.argv >= 3 && String.equal Sys.argv.(2) "-incremental" in

      List.iter (fun (_name, _params, given_spec, body) ->
        if not incremental then begin
          let time_stamp_beforeForward = Sys.time() in
          let inferred_spec = infer_of_expression methods [freshNormalReturnSpec] body in
          let time_stamp_afterForward = Sys.time() in
          let given_spec_n = normalise_spec_list_aux1 given_spec in
          let inferred_spec_n = normalise_spec_list_aux1 inferred_spec in
          let time_stamp_afterNormal = Sys.time() in
          let (res) = entailmentchecking inferred_spec_n given_spec_n in 
          let time_stamp_afterEntail = Sys.time() in


          let given_spec_n = normalise_spec_list_aux2 given_spec_n in
          let inferred_spec_n = normalise_spec_list_aux2 inferred_spec_n in


          let header =
            "\n========== Function: "^ _name ^" ==========\n" ^
            "[Specification] " ^ string_of_spec_list given_spec ^"\n" ^
            "[Normed   Spec] " ^ string_of_spec_list given_spec_n ^"\n\n" ^
            "[Raw Post Spec] " ^ string_of_spec_list inferred_spec ^ "\n" ^
            "[Normed   Post] " ^ string_of_spec_list inferred_spec_n ^"\n\n" ^ 
            "[Forward  Time] " ^ string_of_float ((time_stamp_afterForward -. time_stamp_beforeForward) *. 1000.0 ) ^ " ms\n" ^ 
            "[Normal   Time] " ^ string_of_float ((time_stamp_afterNormal -. time_stamp_afterForward) *. 1000.0) ^ " ms\n"  ^ 
            "[Ential  Check] " ^ 
            (if res then (Pretty.green "true")
             else (Pretty.red "false")) ^ " " ^ string_of_float ((time_stamp_afterEntail  -. time_stamp_afterNormal) *. 1000.0) ^ " ms\n" 

        
          in
          print_string (header);
(* 
          let time_stamp_beforeEntail = Sys.time() in

          let disj_res = Entail.subsumes_disj inferred_spec_n given_spec_n in
          let time_stamp_afterEntail = Sys.time() in
     
          (* let success = List.exists (fun r -> List.for_all (fun (_, _, r1) -> Result.is_ok r1) r) disj_res in *)
          begin match disj_res with
          | Error _ ->
            print_endline (Pretty.red "\n[Verification]")
          | Ok _ ->
            print_endline (Pretty.green "\n[Verification]")
          end;

          Format.printf "%s\n%s\n%s\n%s%s@."
            (string_of_spec_list inferred_spec_n)
            (match disj_res with Ok _ -> Pretty.green "|=" | Error _ -> Pretty.red "|/=")
            (string_of_spec_list given_spec_n)
            (match disj_res with Ok _ -> green "==>\n" | Error _ -> "\n")
            (match disj_res with
              | Ok (pf, _what) ->
                (* string_of_state st ^ "\n\n" ^ *)
                string_of_proof pf
              | Error pf -> string_of_proof pf);

          print_endline ("[Entail   Time] " ^ string_of_float ((time_stamp_afterEntail -. time_stamp_beforeEntail) *. 1000.0) ^ " ms\n")
 *)
                 

          print_endline("")

          (* List.iter (fun dr ->
            (* one of these should succeed *)
            List.iter (fun (s1, s2, res) ->
              (* all of these should succeed *)
              let n1 = normalise_spec s1 |> normalisedStagedSpec2Spec in
              let n2 = normalise_spec s2 |> normalisedStagedSpec2Spec in
          ) disj_res *)
        end else begin
          print_endline "incremental";
        end
      ) methods;

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

