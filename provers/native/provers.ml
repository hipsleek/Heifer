include Hiptypes

(* open Types *)
open Z3

let get_fun_decl ctx s =
  let int = Z3.Arithmetic.Integer.mk_sort ctx in
  let list_int = Z3.Z3List.mk_sort ctx (Z3.Symbol.mk_string ctx "list") int in
  match s with
  | "cons" -> Z3.Z3List.get_cons_decl list_int
  | "head" -> Z3.Z3List.get_head_decl list_int
  | "tail" -> Z3.Z3List.get_tail_decl list_int
  | "is_cons" -> Z3.Z3List.get_is_cons_decl list_int
  | "is_nil" -> Z3.Z3List.get_is_nil_decl list_int
  | _ -> failwith (Format.asprintf "unknown function: %s" s)

let rec term_to_expr ctx : term -> Z3.Expr.expr = function
  | Num n -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
  | Var v -> Z3.Arithmetic.Integer.mk_const_s ctx v
  | UNIT -> Z3.Arithmetic.Integer.mk_const_s ctx "unit"
  | Nil -> Z3.Arithmetic.Integer.mk_const_s ctx "nil"
  (*
  | Gen i          -> Z3.Arithmetic.Real.mk_const_s ctx ("t" ^ string_of_int i ^ "'")
  *)
  | Plus (t1, t2) ->
    Z3.Arithmetic.mk_add ctx [term_to_expr ctx t1; term_to_expr ctx t2]
  | Minus (t1, t2) ->
    Z3.Arithmetic.mk_sub ctx [term_to_expr ctx t1; term_to_expr ctx t2]
  | Eq (t1, t2) ->
    Z3.Boolean.mk_eq ctx (term_to_expr ctx t1) (term_to_expr ctx t2)
  | TTrue -> Z3.Boolean.mk_true ctx
  | TFalse -> Z3.Boolean.mk_false ctx
  | TApp (f, a) ->
    Z3.Expr.mk_app ctx (get_fun_decl ctx f) (List.map (term_to_expr ctx) a)
  | TList _ | TTupple _ -> failwith "term_to_expr"

let rec pi_to_expr ctx : pi -> Expr.expr = function
  | True -> Z3.Boolean.mk_true ctx
  | False -> Z3.Boolean.mk_false ctx
  | Atomic (GT, t1, t2) ->
    let t1 = term_to_expr ctx t1 in
    let t2 = term_to_expr ctx t2 in
    Z3.Arithmetic.mk_gt ctx t1 t2
  | Atomic (GTEQ, t1, t2) ->
    let t1 = term_to_expr ctx t1 in
    let t2 = term_to_expr ctx t2 in
    Z3.Arithmetic.mk_ge ctx t1 t2
  | Atomic (LT, t1, t2) ->
    let t1 = term_to_expr ctx t1 in
    let t2 = term_to_expr ctx t2 in
    Z3.Arithmetic.mk_lt ctx t1 t2
  | Atomic (LTEQ, t1, t2) ->
    let t1 = term_to_expr ctx t1 in
    let t2 = term_to_expr ctx t2 in
    Z3.Arithmetic.mk_le ctx t1 t2
  | Atomic (EQ, t1, t2) ->
    let t1 = term_to_expr ctx t1 in
    let t2 = term_to_expr ctx t2 in
    Z3.Boolean.mk_eq ctx t1 t2
  | Imply (p1, p2) ->
    Z3.Boolean.mk_implies ctx (pi_to_expr ctx p1) (pi_to_expr ctx p2)
  | Predicate (_, _) -> failwith "pi_to_expr"
  (*
  | Atomic (op, t1, t2) -> (
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      match op with
      | Eq -> Z3.Boolean.mk_eq ctx t1 t2
      | LT -> Z3.Arithmetic.mk_lt ctx t1 t2
      | Le -> Z3.Arithmetic.mk_le ctx t1 t2
      | GT -> Z3.Arithmetic.mk_gt ctx t1 t2
      | Ge -> Z3.Arithmetic.mk_ge ctx t1 t2)
      *)
  | And (pi1, pi2) ->
    Z3.Boolean.mk_and ctx [pi_to_expr ctx pi1; pi_to_expr ctx pi2]
  | Or (pi1, pi2) ->
    Z3.Boolean.mk_or ctx [pi_to_expr ctx pi1; pi_to_expr ctx pi2]
  (*| Imply (pi1, pi2)    -> Z3.Boolean.mk_implies ctx (pi_to_expr ctx pi1) (pi_to_expr ctx pi2)
  *)
  | Not pi -> Z3.Boolean.mk_not ctx (pi_to_expr ctx pi)

let z3_query (_s : string) =
  (* Format.printf "z3: %s@." _s; *)
  ()

let check_sat f =
  let debug = false in
  let cfg =
    (if debug then [("model", "false")] else []) @ [("proof", "false")]
  in
  let ctx = mk_context cfg in
  let expr = f ctx in
  (* z3_query (Expr.to_string expr); *)
  if debug then Format.printf "z3: %s@." (Expr.to_string expr);
  (* let goal = Goal.mk_goal ctx true true false in *)
  (* Goal.add goal [ expr ]; *)
  (* let goal = Goal.simplify goal None in *)
  (* if debug then Format.printf "goal: %s@." (Goal.to_string goal); *)
  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [expr];
  z3_query (Z3.Solver.to_string solver);
  let sat = Solver.check solver [expr] == Solver.SATISFIABLE in
  if debug then Format.printf "sat: %b@." sat;
  if debug then begin
    match Solver.get_model solver with
    | None -> Format.printf "no model@."
    | Some m -> Format.printf "model: %s@." (Model.to_string m)
  end;
  sat

let check pi = check_sat (fun ctx -> pi_to_expr ctx pi)

(* see https://discuss.ocaml.org/t/different-z3-outputs-when-using-the-api-vs-cli/9348/3 and https://github.com/Z3Prover/z3/issues/5841 *)
let ex_quantify_expr vars ctx e =
  match vars with
  | [] -> e
  | _ :: _ ->
    Z3.Quantifier.(
      expr_of_quantifier
        (mk_exists_const ctx
           (List.map (Z3.Arithmetic.Integer.mk_const_s ctx) vars)
           e None [] [] None None))

(** check if [p1 => ex vs. p2] is valid. this is a separate function which doesn't cache results because exists isn't in pi *)
let entails_exists p1 vs p2 =
  let f ctx =
    let r =
      Z3.Boolean.mk_not ctx
        (Z3.Boolean.mk_implies ctx (pi_to_expr ctx p1)
           (ex_quantify_expr vs ctx (pi_to_expr ctx p2)))
    in
    (* Format.printf "oblig: %s@." (Expr.to_string r); *)
    r
  in
  not (check_sat f)

let valid p =
  let f ctx = Z3.Boolean.mk_not ctx (pi_to_expr ctx p) in
  not (check_sat f)

let (historyTable : (string * bool) list ref) = ref []
let hash_pi pi = string_of_int (Hashtbl.hash pi)

let rec existInhistoryTable pi table =
  match table with
  | [] -> None
  | (x, b) :: xs ->
    if String.compare x (hash_pi pi) == 0 then Some b
    else existInhistoryTable pi xs

let counter : int ref = ref 0

let askZ3 pi =
  match existInhistoryTable pi !historyTable with
  | Some b -> b
  | None ->
    let _ = counter := !counter + 1 in
    let re = check pi in
    let () = historyTable := (hash_pi pi, re) :: !historyTable in
    re

let handle f = f ()
