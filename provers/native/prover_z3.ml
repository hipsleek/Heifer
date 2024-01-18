open Hipcore
open Debug
open Hiptypes
open Pretty

(* open Types *)
open Z3

let list_int_sort ctx =
  let int = Z3.Arithmetic.Integer.mk_sort ctx in
  (* Z3.Z3List.mk_sort ctx (Z3.Symbol.mk_string ctx "List") int *)
  Z3.Z3List.mk_list_s ctx "List" int

let unit_sort ctx =
  let us = Z3.Symbol.mk_string ctx "unit" in
  Z3.Tuple.mk_sort ctx us [] []

let get_fun_decl ctx s =
  let list_int = list_int_sort ctx in
  match s with
  | "cons" -> (Z3.Z3List.get_cons_decl list_int)
  | "head" -> (Z3.Z3List.get_head_decl list_int)
  | "tail" -> (Z3.Z3List.get_tail_decl list_int)
  | "is_cons" -> (Z3.Z3List.get_is_cons_decl list_int)
  | "is_nil" -> (Z3.Z3List.get_is_nil_decl list_int)
  | _ ->  (* ASK Darius *)
    let intSort = (Z3.Arithmetic.Integer.mk_sort ctx) in 
    if String.compare s "effNo" == 0 then Z3.FuncDecl.mk_func_decl_s ctx "effNo" [intSort] intSort
    else failwith (Format.asprintf "unknown function 1: %s" s)

let rec term_to_expr env ctx t : Z3.Expr.expr =
  match t with
  | Num n -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
  | Var v ->
    (match SMap.find_opt v env with
    | None ->
      (* failwith (Format.asprintf "could not infer type for variable: %s" v) *)
      (* default to int *)
      Z3.Arithmetic.Integer.mk_const_s ctx v
    | Some t1 ->
      (* Format.printf "%s : %s@." v
         (match t1 with
         | Int -> "Int"
         | List_int -> "List_int"
         | Unit -> "unit"
         | Bool -> "Bool"
         | TVar _ -> "tvar"); *)
      (match t1 with
      | TVar _ ->
        (* failwith (Format.asprintf "could not infer type for variable: %s" v) *)
        (* default to int *)

        Z3.Arithmetic.Integer.mk_const_s ctx v
      | Int | Lamb ->
        (* Format.printf "%s is int@." v; *)


        let res = Z3.Arithmetic.Integer.mk_const_s ctx v in 

        res
      | Unit ->
        Z3.Expr.mk_const_s ctx "unit" (unit_sort ctx)
      | List_int ->
        (* Format.printf "%s is list@." v; *)
        let list_int = list_int_sort ctx in
        Z3.Expr.mk_const_s ctx v list_int
      | Bool -> Z3.Boolean.mk_const_s ctx v
      | Arrow (_, _) -> failwith "arrow not implemented"))
  | UNIT ->
    let mk = Z3.Tuple.get_mk_decl (unit_sort ctx) in 
    Z3.Expr.mk_app ctx mk []
  | TLambda _ ->
    (* Format.printf "z3 %s %d@." (string_of_term t) (hash_lambda t); *)
    Z3.Arithmetic.Integer.mk_numeral_i ctx (Subst.hash_lambda t)
  | Nil ->
    let list_int = list_int_sort ctx in
    Z3.Z3List.nil list_int
  (*
  | Gen i          -> Z3.Arithmetic.Real.mk_const_s ctx ("t" ^ string_of_int i ^ "'")
  *)
  | Plus (t1, t2) ->
    (*print_endline ("\n-------\nPlus " ^ string_of_term t);*)
    let t1' = term_to_expr env ctx t1 in 
    let t2' = term_to_expr env ctx t2 in 
    let res = Z3.Arithmetic.mk_add ctx [t1'; t2'] in 


    (*Here!!!! 
    mk_add
    Plus v85, (^ 2 n) ===> Plus (+ (to_real v85) (^ 2 n))
*)

    (*let res = Z3.Arithmetic.Real.mk_real2int ctx res in 
    *)
    
    (*print_endline ("Plus " ^ Expr.to_string t1' ^ ", " ^ Expr.to_string t2');
    print_endline ("Plus " ^ Expr.to_string res );
    *)

    res
  | Minus (t1, t2) ->
    Z3.Arithmetic.mk_sub ctx [term_to_expr env ctx t1; term_to_expr env ctx t2]

  | Rel (bop, t1, t2) ->
    (match bop with
    | EQ ->
      Z3.Boolean.mk_eq ctx (term_to_expr env ctx t1) (term_to_expr env ctx t2)
    | GT ->
      Z3.Arithmetic.mk_gt ctx (term_to_expr env ctx t1)
        (term_to_expr env ctx t2)
    | LT ->
      Z3.Arithmetic.mk_lt ctx (term_to_expr env ctx t1)
        (term_to_expr env ctx t2)
    | GTEQ ->
      Z3.Arithmetic.mk_ge ctx (term_to_expr env ctx t1)
        (term_to_expr env ctx t2)
    | LTEQ ->
      Z3.Arithmetic.mk_le ctx (term_to_expr env ctx t1)
        (term_to_expr env ctx t2))
  | TTrue -> Z3.Boolean.mk_true ctx
  | TFalse -> Z3.Boolean.mk_false ctx
  | TNot a -> Z3.Boolean.mk_not ctx (term_to_expr env ctx a)
  | TAnd (a, b) ->
    Z3.Boolean.mk_and ctx [term_to_expr env ctx a; term_to_expr env ctx b]
  | TOr (a, b) ->
    Z3.Boolean.mk_or ctx [term_to_expr env ctx a; term_to_expr env ctx b]
  | TCons (a, b) ->
    Z3.Expr.mk_app ctx (get_fun_decl ctx "cons")
      (List.map (term_to_expr env ctx) [a; b])
  | TApp (f, a) ->
    Z3.Expr.mk_app ctx (get_fun_decl ctx f) (List.map (term_to_expr env ctx) a)
  | TPower (Num 2, Var "n") -> 
      Z3.Arithmetic.Integer.mk_const_s ctx "v2N"
  | TPower (Num 2, Plus(Var "n", Num 1)) -> 
      Z3.Arithmetic.Integer.mk_const_s ctx "v2Nplus1"

  | TPower (Num n, Plus (Num n1, Num n2)) -> 
      let rec power base exp = 
        match exp with 
        | 0 -> 1 
        | n -> base * (power base (n-1))
      in 
      Z3.Arithmetic.Integer.mk_numeral_i ctx (power n (n1+ n2))


  | TPower (t1, t2) -> 
    print_endline ("TPower "^ string_of_term t);
    
    let res = Z3.Arithmetic.mk_power ctx (term_to_expr env ctx t1) (term_to_expr env ctx t2) in 
    (*print_endline ("TPower " ^ Expr.to_string res);*)
    res
  
  
  | TTimes (t1, t2) -> Z3.Arithmetic.mk_mul ctx [term_to_expr env ctx t1; term_to_expr env ctx t2]
  | TDiv (t1, t2) -> Z3.Arithmetic.mk_div ctx (term_to_expr env ctx t1) (term_to_expr env ctx t2)

  | TList _ | TTupple _ -> failwith "term_to_expr"

let rec pi_to_expr env ctx pi: Expr.expr = 
  match pi with 
  | True -> Z3.Boolean.mk_true ctx
  | False -> Z3.Boolean.mk_false ctx
  | Atomic (GT, t1, t2) ->
    let t1 = term_to_expr env ctx t1 in
    let t2 = term_to_expr env ctx t2 in
    Z3.Arithmetic.mk_gt ctx t1 t2
  | Atomic (GTEQ, t1, t2) ->
    let t1 = term_to_expr env ctx t1 in
    let t2 = term_to_expr env ctx t2 in
    Z3.Arithmetic.mk_ge ctx t1 t2
  | Atomic (LT, t1, t2) ->
    let t1 = term_to_expr env ctx t1 in
    let t2 = term_to_expr env ctx t2 in
    Z3.Arithmetic.mk_lt ctx t1 t2
  | Atomic (LTEQ, t1, t2) ->
    let t1 = term_to_expr env ctx t1 in
    let t2 = term_to_expr env ctx t2 in
    Z3.Arithmetic.mk_le ctx t1 t2
  (* | IsCons (v, t1, t2) -> *)
    (* failwith "" *)
  | Atomic (EQ, t1, t2) ->
    let t1 = term_to_expr env ctx t1 in
    let t2 = term_to_expr env ctx t2 in
    (*print_endline ("\n======\nAtomic EQ " ^ Expr.to_string t1);
    print_endline ("Atomic EQ " ^ Expr.to_string t2);
    *)
    let res = Z3.Boolean.mk_eq ctx t1 t2 in 
    res

  | Imply (p1, p2) ->
    Z3.Boolean.mk_implies ctx (pi_to_expr env ctx p1) (pi_to_expr env ctx p2)
  | Predicate (_, _) -> failwith "pi_to_expr"
  | Subsumption (_, _) -> pi_to_expr env ctx True
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
    Z3.Boolean.mk_and ctx [pi_to_expr env ctx pi1; pi_to_expr env ctx pi2]
  | Or (pi1, pi2) ->
    Z3.Boolean.mk_or ctx [pi_to_expr env ctx pi1; pi_to_expr env ctx pi2]
  (*| Imply (pi1, pi2)    -> Z3.Boolean.mk_implies ctx (pi_to_expr env ctx pi1) (pi_to_expr env ctx pi2)
  *)
  | Not pi -> Z3.Boolean.mk_not ctx (pi_to_expr env ctx pi)

(* let z3_query (_s : string) =
   (* Format.printf "z3: %s@." _s; *)
   () *)

(* let _test () =
  let ctx = Z3.mk_context [] in
  (* let int = Z3.Arithmetic.Integer.mk_sort ctx in *)
  let list_int = list_int_sort ctx in
  let left =
    (* Z3.Boolean.mk_eq ctx
       (Z3.Arithmetic.Integer.mk_const_s ctx "a")
       (Z3.Arithmetic.Integer.mk_numeral_i ctx 1) *)
    Z3.Boolean.mk_and ctx
      [
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "a" list_int)
          (Z3.Z3List.nil list_int);
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "c" list_int)
          (Z3.Z3List.nil list_int);
      ]
  in
  let right =
    (* Z3.Boolean.mk_eq ctx
       (Z3.Arithmetic.Integer.mk_const_s ctx "b")
       (Z3.Arithmetic.Integer.mk_numeral_i ctx 1) *)
    Z3.Boolean.mk_and ctx
      [
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "b" list_int)
          (Z3.Z3List.nil list_int);
        Z3.Boolean.mk_eq ctx
          (Z3.Expr.mk_const_s ctx "d" list_int)
          (Z3.Z3List.nil list_int);
      ]
  in
  let expr =
    Z3.Boolean.mk_not ctx
      (Z3.Boolean.mk_implies ctx left
         Z3.Quantifier.(
           expr_of_quantifier
             (mk_exists_const ctx
                [
                  Z3.Expr.mk_const_s ctx "b" list_int;
                  Z3.Expr.mk_const_s ctx "d" list_int
                  (* Z3.Expr.mk_const_s ctx "b" int *)
                  (* Z3.Arithmetic.Integer.mk_const_s ctx "b"; *);
                ]
                right None [] [] None None)))
  in
  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [expr];
  debug ~at:4 ~title:"z3 expr" "%s" (Expr.to_string expr);
  debug ~at:4 ~title:"z3 solver" "%s" (Solver.to_string solver);
  let sat = Solver.check solver [] == Solver.SATISFIABLE in
  debug ~at:4 ~title:"sat?" "%b" sat;
  match Solver.get_model solver with
  | None -> debug ~at:4 ~title:"no model" ""
  | Some m -> debug ~at:4 ~title:"model" "%s" (Model.to_string m) *)

let check_sat f =
  let@ _ = Globals.Timing.(time z3) in 
  let cfg =
    let debug = false in
    (if debug then [("model", "false")] else []) @ [("proof", "false")]
  in
  let ctx = mk_context cfg in
  Z3.Params.update_param_value ctx "timeout" "5000";
  let expr =
    let@ _ = Debug.span (fun _ -> debug ~at:4 ~title:"build formula" "") in
    f ctx
  in
  (* let goal = Goal.mk_goal ctx true true false in *)
  (* Goal.add goal [ expr ]; *)
  (* let goal = Goal.simplify goal None in *)
  (* if debug then Format.printf "goal: %s@." (Goal.to_string goal); *)
  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [expr];
  (* print both because the solver does some simplification *)
  debug ~at:4 ~title:"z3 expr" "%s\n(check-sat)" (Expr.to_string expr);
  let@ _ =
    Debug.span (fun _ -> debug ~at:5 ~title:"z3 solver" "%s\n(check-sat)" (Solver.to_string solver))
  in
  (* Format.printf "%s@." (Solver.to_string solver); *)
  (* Format.printf "%s@." (Expr.to_string expr); *)
  let status =
    let@ _ =
      Debug.span (fun r ->
          debug ~at:4
            ~title:"z3 sat check"
            "%s" (string_of_result Solver.string_of_status r))
    in
    Solver.check solver []
  in 
  (* (match Solver.get_model solver with
  | None -> debug ~at:4 ~title:"no model" ""
  | Some m -> debug ~at:4 ~title:"model" "%s" (Model.to_string m)); *)
  status


(* let check env pi =
  debug ~at:4 ~title:"z3 sat, pi" "%s" (string_of_pi pi);
  check_sat (fun ctx -> pi_to_expr env ctx pi) *)

(* see https://discuss.ocaml.org/t/different-z3-outputs-when-using-the-api-vs-cli/9348/3 and https://github.com/Z3Prover/z3/issues/5841 *)
let ex_quantify_expr env vars ctx e =
  match vars with
  | [] -> e
  | _ :: _ ->
    Z3.Quantifier.(
      expr_of_quantifier
        (mk_exists_const ctx
           (List.map (fun v -> term_to_expr env ctx (Var v)) vars)
           e None [] [] None None))


(* this is a separate function which doesn't cache results because exists isn't in pi *)
let entails_exists_inner env p1 vs p2 =
  debug ~at:4 ~title:"z3 valid" "%s => ex %s. %s\n%s" (string_of_pi p1)
    (String.concat " " vs) (string_of_pi p2) (string_of_typ_env env);
  let f ctx =
    let r =
      Z3.Boolean.mk_not ctx
        (Z3.Boolean.mk_implies ctx (pi_to_expr env ctx p1)
           (ex_quantify_expr env vs ctx (pi_to_expr env ctx p2)))
    in
    (* Format.printf "oblig: %s@." (Expr.to_string r); *)
    r
  in
  match check_sat f with 
  | UNSATISFIABLE -> true
  |	UNKNOWN |	SATISFIABLE -> false

let entails_exists1 env p1 vs p2 =
  (*
  print_endline (string_of_bool ( allDisjunctions p2)); 
  print_endline (string_of_bool ( existPurePattern p2 p1)); 

  (* this is a trick because z3 can not handle when there are power operators exist, 
     for cases that n>=0 => n>=0 /\ ... , it will right away return true *)
  if allDisjunctions p2 && existPurePattern p2 p1 then true 
  else 
  *)

  (* darius: temporarily disabled because this makes the new ens false; ... normalization very slow, the right way is prob to add an axiom declaration so we can declare these extra assumptions where they are needed *)
  (* let p1 = 
    if entails_exists_inner env p1 vs (Atomic(EQ, Var "n", Num 0)) then 
      let retation_v2Nplus1_is_2 = (Atomic(EQ, Var "v2Nplus1", Num 2)) in 
      And (retation_v2Nplus1_is_2, p1) 
    else if entails_exists_inner  env p1 vs (Atomic(EQ, Var "n", Num 1)) then 
      let retation_v2Nplus1_is_4 = (Atomic(EQ, Var "v2Nplus1", Num 4)) in 
      And (retation_v2Nplus1_is_4, p1) 
    else
      let retation_v2N_v2Nplus1 = Atomic (EQ, (Var "v2Nplus1"), Plus (Var "v2N", Var "v2N"))in 
      And (retation_v2N_v2Nplus1, p1) 
  in  *)

  (*
  Format.printf "entails_exists_inner, pi: %s => %s@." (string_of_pi p1) (string_of_pi p2);
  *)
  entails_exists_inner env p1 vs p2

let entails_exists env p1 vs p2 =
  if Debug.in_debug_mode () then
    entails_exists1 env p1 vs p2
  else
    try
      entails_exists1 env p1 vs p2
    with e ->
      (* the stack trace printed is not the same (and is much less helpful) if the exception is caught *)
      Debug.debug ~at:1 ~title:"an error occurred, assuming proof failed"
      "%s" (Printexc.to_string e);
      (* Printexc.print_backtrace stdout; *)
      false

(* let _valid p =
  let f ctx = Z3.Boolean.mk_not ctx (pi_to_expr SMap.empty ctx p) in
  not (check_sat f) *)

(* let (historyTable : (string * bool) list ref) = ref [] *)
(* let hash_pi pi = string_of_int (Hashtbl.hash pi) *)

(* let rec existInhistoryTable pi table =
  match table with
  | [] -> None
  | (x, b) :: xs ->
    if String.compare x (hash_pi pi) == 0 then Some b
    else existInhistoryTable pi xs

let counter : int ref = ref 0 *)

(* let _askZ3 env pi =
  match existInhistoryTable pi !historyTable with
  | Some b -> b
  | None ->
    let _ = counter := !counter + 1 in
    let re = check env pi in
    let () = historyTable := (hash_pi pi, re) :: !historyTable in
    re *)
