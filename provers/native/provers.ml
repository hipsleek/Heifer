include Types

(* open Types *)
open Z3

let rec term_to_expr ctx : term -> Z3.Expr.expr = function
  | Num n -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
  | Var v -> Z3.Arithmetic.Integer.mk_const_s ctx v
  | UNIT -> Z3.Arithmetic.Integer.mk_const_s ctx "unit"
  (*
  | Gen i          -> Z3.Arithmetic.Real.mk_const_s ctx ("t" ^ string_of_int i ^ "'")
  *)
  | Plus (t1, t2) ->
    Z3.Arithmetic.mk_add ctx [term_to_expr ctx t1; term_to_expr ctx t2]
  | Minus (t1, t2) ->
    Z3.Arithmetic.mk_sub ctx [term_to_expr ctx t1; term_to_expr ctx t2]
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

let z3_query (_ : string) = ()

let check_sat ?(debug = false) f =
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

let check ?debug pi = check_sat ?debug (fun ctx -> pi_to_expr ctx pi)

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

(* ?(debug = false) *)

(** check if [p1 => ex vs. p2] is valid. this is a separate function which doesn't cache results because exists isn't in pi *)
let entails_exists p1 vs p2 =
  let f ctx =
    Z3.Boolean.mk_not ctx
      (Z3.Boolean.mk_implies ctx (pi_to_expr ctx p1)
         (ex_quantify_expr vs ctx (pi_to_expr ctx p2)))
  in
  not (check_sat ~debug:false f)

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

let rec normalPure (pi : pi) : pi =
  match pi with
  | And (p1, p2) ->
    let p1 = normalPure p1 in
    let p2 = normalPure p2 in
    (match (p1, p2) with
    | True, _ -> p2
    | _, True -> p1
    | False, _ -> False
    | _, False -> False
    | _, _ -> And (p1, p2))
  | Or (p1, p2) ->
    let p1 = normalPure p1 in
    let p2 = normalPure p2 in
    (match (p1, p2) with
    | True, _ -> True
    | _, True -> True
    | False, _ -> p2
    | _, False -> p1
    | _, _ -> Or (p1, p2))
  | Not p1 -> Not (normalPure p1)
  | _ -> pi

let handle f = f ()
