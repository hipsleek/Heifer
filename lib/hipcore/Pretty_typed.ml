(* Functions for printing the typed AST. *)

open Common
open Typedhip
open Types

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

exception Foo of string


let colours : [`Html|`Ansi|`None] ref = ref `None

let col ~ansi ~html text =
  (match !colours with
  | `None -> ""
  | `Ansi -> ansi
  | `Html -> html) ^ text ^
  (match !colours with
  | `None -> ""
  | `Ansi -> "\u{001b}[0m"
  | `Html -> "</span>")

let red text = col ~ansi:"\u{001b}[31m" ~html:"<span class=\"output-error\">" text
let green text = col ~ansi:"\u{001b}[32m" ~html:"<span class=\"output-ok\">" text
let yellow text = col ~ansi:"\u{001b}[33m" ~html:"<span class=\"output-emph\">" text

let end_of_var = Str.regexp "_?[0-9]+$"

let string_of_type = Pretty.string_of_type

let string_of_binder ((ident, typ) : binder) =
  Format.sprintf "(%s : %s)" ident (string_of_type typ)

let string_of_args pp args =
  match args with
  | [] -> "()"
  | _ ->
    let a = String.concat ", " (List.map pp args) in
    Format.asprintf "(%s)" a

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




let string_of_bin_op op : string =
  match op with
  | GT -> ">"
  | LT -> "<"
  | EQ -> "="
  | GTEQ -> ">="
  | LTEQ -> "<="

let string_of_constr_call n args =
  match n, args with
  | "[]", _ -> "[]"
  | "::", [a1; a2] -> Format.asprintf "%s :: %s" (string_of_binder a1) (string_of_binder a2)
  | _ -> Format.asprintf "%s(%s)" n (String.concat ", " (List.map string_of_binder args))

let rec string_of_term t : string =
  Pretty.string_of_term (Untypehip.untype_term t)

and string_of_staged_spec s = Pretty.string_of_staged_spec (Untypehip.untype_staged_spec s)

and string_of_kappa (k:kappa) : string =
  match k with
  | EmptyHeap -> "emp"
  | PointsTo  (str, args) -> Format.sprintf "%s->%s" str (List.map string_of_term [args] |> String.concat ", ")
  | SepConj (k1, k2) -> string_of_kappa k1 ^ "*" ^ string_of_kappa k2
  (*| MagicWand (k1, k2) -> "(" ^ string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  ^ ")" *)
  (* | Implication (k1, k2) -> string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  *)

and string_of_state (p, h) : string =
  match h, p with
  | _, True -> string_of_kappa h
  | EmptyHeap, _ -> string_of_pi p
  | _ ->
    Format.asprintf "%s/\\%s" (string_of_kappa h) (string_of_pi p)
    (* Format.asprintf "%s*%s" (string_of_kappa h) (string_of_pi p) *)

and string_of_pi pi : string =
  match pi with
  | True -> "T"
  | False -> "F"
  | Atomic (op, t1, t2) -> string_of_term t1 ^ string_of_bin_op op ^ string_of_term t2
  | And   (p1, p2) -> string_of_pi p1 ^ "/\\" ^ string_of_pi p2
  | Or     (p1, p2) -> string_of_pi p1 ^ "\\/" ^ string_of_pi p2
  | Imply  (p1, p2) -> string_of_pi p1 ^ "=>" ^ string_of_pi p2
  | Not    p -> "not(" ^ string_of_pi p ^ ")"
  | Predicate (str, t) -> str ^ "(" ^ (string_of_args string_of_term t) ^ ")"
  | Subsumption (a, b) -> Format.asprintf "%s <: %s" (string_of_term a) (string_of_term b)

and string_of_try_catch_lemma (x:tryCatchLemma) : string = 
  let (tcl_head, tcl_handledCont, (*(h_normal, h_ops),*) tcl_summary) = x in 
  "TRY " 
  ^ 
  string_of_staged_spec tcl_head 

  ^ (match tcl_handledCont with 
  | None -> "" | Some conti -> " # " ^ string_of_staged_spec conti)

  
  ^ " CATCH \n" (*^ string_of_handlingcases (h_normal, h_ops ) *)
  ^ "=> " ^ string_of_staged_spec tcl_summary

and string_of_handler_type (h:handler_type) : string = 
    match h with
    | Deep -> "d"
    | Shallow -> "s"

and string_of_core_lang (e:core_lang) :string = Pretty.string_of_core_lang (Untypehip.untype_core_lang e)

let find_rec p_name =
  object(self)
    inherit [_] reduce_spec as super
    method zero = false
    method plus = (||)

    method! visit_HigherOrder _ f a =
      self#plus (f = p_name) (super#visit_HigherOrder () f a)

    method! visit_Atomic () op a b =
      match op with
      | EQ -> (match (a.term_desc, b.term_desc) with
        | (Var x, Var y) -> x = p_name || y = p_name
        | _ -> false)
      | _ -> false
  end

(**********************************************)
let string_of_existentials vs =
  match vs with
  | [] -> ""
  | _ :: _ -> Format.asprintf "ex %s. " (String.concat "," (List.map string_of_binder vs))

let string_of_res b = if b then green "true" else red "false"

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

let string_of_lemma l =
  Format.asprintf "%s: forall %s, %s <: %s" l.l_name (string_of_list string_of_binder l.l_params) (string_of_staged_spec l.l_left) (string_of_staged_spec l.l_right)

(* let string_of_time = string_of_float *)
let string_of_time = Format.asprintf "%.0f"

let string_of_sset s =
  Format.asprintf "{%s}" (String.concat ", " (SSet.elements s))

let string_of_smap pp s =
  Format.asprintf "{%s}" (String.concat ", " (List.map (fun (k, v) -> Format.asprintf "%s -> %s" k (pp v)) (SMap.bindings s)))

let conj xs =
  match xs with
  | [] -> True
  | x :: xs -> List.fold_right (fun c t -> And (c, t)) xs x

let string_of_pure_fn ({ pf_name; pf_params; pf_ret_type; pf_body } : pure_fn_def) : string =
  Format.asprintf "let %s %s : %s = %s" pf_name (String.concat " " (List.map (fun (p, t) -> Format.asprintf "(%s:%s)" p (string_of_type t)) pf_params)) (string_of_type pf_ret_type) (string_of_core_lang pf_body)

let string_of_tmap pp s =
  Format.asprintf "{%s}" (String.concat ", " (List.map (fun (k, v) -> Format.asprintf "%s -> %s" (string_of_type k) (pp v)) (TMap.bindings s)))

let string_of_abs_env t = Pretty.string_of_abs_env t
  (* "<opaque>" *)

let string_of_typ_env t =
  Format.asprintf "%s" (string_of_smap string_of_type t)


let string_of_quantified to_s (vs, e) =
  match vs with
  | [] -> to_s e
  | _ :: _ -> Format.asprintf "ex %s. %s" (String.concat " " vs) (to_s e)

let string_of_instantiations pv kvs =
  List.map (fun (k, v) -> Format.asprintf "%s := %s" k (pv v)) kvs
  |> String.concat ", " |> Format.asprintf "[%s]"

let string_of_bindings = string_of_instantiations

let string_of_meth_def m =
  Format.asprintf "let rec %s %s\n%s=\n%s" m.m_name
    (match m.m_params with | [] -> "()" | _ -> String.concat " " (List.map string_of_binder m.m_params))
    ((match m.m_spec with None -> "" | Some s -> s |> string_of_staged_spec |> (Format.asprintf "(*@@ %s @@*)\n")))
    (string_of_core_lang m.m_body)

let string_of_program (cp:core_program) :string =
  List.map string_of_meth_def cp.cp_methods |> String.concat "\n\n"

