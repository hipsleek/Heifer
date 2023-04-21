
open List
open Hiptypes
open Pretty
(* open Z3 *)

(* 
let rec term_to_expr ctx : term -> Expr.expr = function
  | Num n        -> Arithmetic.Integer.mk_numeral_i ctx n
  | Var v          -> Arithmetic.Integer.mk_const_s ctx v
  | Plus (t1, t2)  -> Arithmetic.mk_add ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]
  | Minus (t1, t2) -> Arithmetic.mk_sub ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]
  | TTupple _ | TList _ | UNIT -> raise (Foo "Rewriting.ml->term_to_expr") 

let rec pi_to_expr ctx : pi -> Expr.expr = function
  | True                -> Boolean.mk_true ctx
  | False               -> Boolean.mk_false ctx
  | Atomic (op, t1, t2) -> (
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      match op with
      | EQ -> Boolean.mk_eq ctx t1 t2
      | LT -> Arithmetic.mk_lt ctx t1 t2
      | LTEQ -> Arithmetic.mk_le ctx t1 t2
      | GT -> Arithmetic.mk_gt ctx t1 t2
      | GTEQ -> Arithmetic.mk_ge ctx t1 t2)
  | And (pi1, pi2)      -> Boolean.mk_and ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | Or (pi1, pi2)       -> Boolean.mk_or ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | Imply (pi1, pi2)    -> Boolean.mk_implies ctx (pi_to_expr ctx pi1) (pi_to_expr ctx pi2)
  | Not pi              -> Boolean.mk_not ctx (pi_to_expr ctx pi)
  | Predicate _ -> raise (Foo "Rewriting.ml->pi_to_expr")


let check p1 p2 : bool =
  let pi =   (Not (Or (Not p1, p2))) in
  let cfg = [ ("model", "false"); ("proof", "false") ] in
  let ctx = mk_context cfg in
  let expr = pi_to_expr ctx pi in
  (* print_endline (Expr.to_string expr); *)

  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [ expr ];
  let sat = not (Solver.check solver [] == Solver.SATISFIABLE) in
  (*print_endline (Solver.to_string solver); *)
  sat *)

(* let check_pure p1 p2 : (bool * string) = 
  let sat = check  p1 p2 in
  let _ = string_of_pi p1 ^" => " ^ string_of_pi p2 in 
  let buffur = ("[PURE]"(*^(pure)*)^ " " ^(if sat then "Succeed\n" else "Fail\n")  )
  in (sat, buffur) *)



let rec checkexist lst super: bool = 
  match lst with
  | [] -> true
  | x::rest  -> if List.mem x super then checkexist rest super
  else false 
  ;;


let comparePointsTo (s1, t1) (s2, t2) : bool = 
  let rec helper t1 t2 : bool = 
    match (t1, t2) with 
    | ([], []) -> true 
    | (x::xs, y::ys)  -> x == y && helper xs ys
    | _ -> false 
  in 
  (String.compare s1 s2 == 0) && helper t1 t2


let compareKappa (k1:kappa) (k2:kappa) : bool = 
  match (k1, k2) with 
  | (EmptyHeap, EmptyHeap) -> true 
  | (PointsTo pt1, PointsTo pt2) -> 
    (*print_string ("compayring " ^ string_of_kappa k1 ^ " and " ^  
    string_of_kappa k2 ^ " = " ^ string_of_bool (pt1 = pt2) ^"\n");*)
    pt1 = pt2
    (*comparePointsTo pt1 == pt2*)
  | (SepConj _, SepConj _)
  (* | (Implication _, Implication _) -> raise (Foo "compareKappa TBD") *)
  | _ -> false


let comparePure (p1:pi) (p2:pi) : bool = 
  match (p1, p2) with 
  | (True, True)
  | (False, False) -> true 
  | (Atomic (op1, t1, t2), Atomic (op2, t3, t4)) -> 
     op1 == op2 && t1 == t3 && t2 == t4 
  | (And _, And _) 
  | (Or _, Or _) 
  | (Imply _, Imply _) 
  | (Not _, Not _) -> raise (Foo "comparePure TBD")
  | _ -> false





let  check_containment (_:spec) (_:spec) :(bool * binary_tree) = failwith "TBD check_containment"

;;


let printReport (_:spec) (_:spec) :(bool * float * string) =  failwith "TBD printReport"
(*
  let startTimeStamp = Sys.time() in
  let (tLHS, cLHS) = partionTraceAndCOncrteTrace lhs in 
  let (tRHS, cRHS) = partionTraceAndCOncrteTrace rhs in 

  let (re, tree) = check_containment tLHS tRHS in 
  let (re1, tree1) = check_concreteEntaill cLHS cRHS in 
  let computtaion_time = ((Sys.time() -. startTimeStamp) *. 1000.0) in 
  let verification_time = "[TRS Time: " ^ string_of_float (computtaion_time) ^ " ms]" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children (Node ("root", [tree;tree1])) in

  let whole = "[TRS Result: " ^ (if re && re1 then "Succeed" else "Fail" ) in 
  (re, computtaion_time, "~~~~~~~~~~~~~~~~~~~~~\n" ^
  verification_time  ^"\n"^
  whole  ^"\n"^
  "- - - - - - - - - - - - - -"^"\n" ^
  result)
  *)
  ;;


let n_GT_0 : pi =
  Atomic (LT, Var "n", Num 0)

let n_GT_1 : pi =
  Atomic (LT, Var "n", Num 5)







