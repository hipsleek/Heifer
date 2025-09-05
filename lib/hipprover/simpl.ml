(** Apply mechanical simplification rules to the given elements.*)
open Hipcore_typed
open Typedhip
open Rewriting
open Syntax
open Utils.Hstdlib

let term_num_folding_rules = 
  let num_constant_folding_rule op f =
    let open Rules.Term in
    dynamic_rule (binop op (uvar "a" ~typ:Int) (uvar "b" ~typ:Int))
      (fun sub ->
        let a = of_uterm (sub "a") in
        let b = of_uterm (sub "b") in
        match a.term_desc, b.term_desc with
        | Const (Num a), Const (Num b) -> num (f a b)
        | _, _ -> binop op a b)
  in
  [ num_constant_folding_rule Plus (+);
    num_constant_folding_rule Minus (-);
    num_constant_folding_rule TTimes ( * );
    num_constant_folding_rule TDiv (/); ]

let term_rewrites = term_num_folding_rules

let simplify_term (t : term) =
  autorewrite term_rewrites (Term t) |> Rules.Term.of_uterm

let pure_and_folding_rules = Rules.Pure.[
  rule (And (True, uvar "p")) (uvar "p");
  rule (And (uvar "p", True)) (uvar "p");
  rule (And (False, uvar "p")) False;
  rule (And (uvar "p", False)) False;
]

let pure_or_folding_rules = Rules.Pure.[
  rule (Or (False, uvar "p")) (uvar "p");
  rule (Or (uvar "p", False)) (uvar "p");
  rule (Or (uvar "p", True)) True;
  rule (Or (True, uvar "p")) True;
]

let pure_not_folding_rules = Rules.Pure.[
  rule (Not False) True;
  rule (Not True) False
]

let pure_rewrites = List.concat [
  pure_and_folding_rules;
  pure_or_folding_rules;
  pure_not_folding_rules;
]

let simplify_pure (p : pi) =
  let database = pure_rewrites @ term_rewrites in
  autorewrite database (Pure p) |> Rules.Pure.of_uterm

let kappa_emp_folding_rules = Rules.Heap.[
  rule (SepConj (EmptyHeap, (uvar "k"))) (uvar "k");
  rule (SepConj (uvar "k", EmptyHeap)) (uvar "k")]

let kappa_rewrites = kappa_emp_folding_rules

let simplify_kappa (h : kappa) =
  let database = kappa_rewrites @ term_rewrites in
  autorewrite database (Heap h) |> Rules.Heap.of_uterm

let simplify_spec (s : staged_spec) =
  let database = pure_rewrites @ kappa_rewrites @ term_rewrites in
  autorewrite database (Staged s) |> Rules.Staged.of_uterm

let is_contradiction_kappa (h : kappa) =
  let hs = conjuncts_of_kappa h in
  let rec check ps = function
    | [] -> false
    | PointsTo (p, _) :: _ when SSet.mem p ps -> true
    | PointsTo (p, _) :: hs -> check (SSet.add p ps) hs
    | _ -> failwith "is_contradiction_kappa.check"
  in
  check SSet.empty hs

let is_contradiction_pure (p : pi) =
  let ps = conjuncts_of_pi p in
  (* we only detect inequalities between two terms that are exactly equal at the moment. *)
  (* there can be other contradictions in our formula, like 2 < 1. But we will not handle
     it at the moment. *)
  let rec check = function
    | [] -> false
    | Not (Atomic (EQ, t1, t2)) :: _ when t1 = t2 -> true
    | _ :: ps -> check ps
  in
  check ps

let%expect_test "simplify tests" =
  let test simpl printer v =
    Format.printf "simplify: %s@." (printer v);
    Format.printf "result: %s@." (printer (simpl v))
  in
  let h1 =  (SepConj (EmptyHeap, SepConj (PointsTo ("x", num 1), EmptyHeap))) in
  test simplify_kappa Pretty.string_of_kappa h1;
  [%expect {|
    simplify: emp * x -> 1 * emp
    result: x -> 1
    |}];
  
  let ( -@ ) = binop Minus in
  let ( *@ ) = binop TTimes in
  let ( +@ ) = binop Plus in
  let t = (num 5) *@ ((num 6) +@ ((num 10) -@ (num 3))) in
  test simplify_term Pretty.string_of_term t;
  [%expect {|
    simplify: 5 *. (6 + 10 - 3)
    result: 65
    |}];

  let p1 = And (True, Or ( And (False, eq (var "a") (var "b")), eq (var "x") (var "y"))) in
  test simplify_pure Pretty.string_of_pi p1;
  [%expect {|
    simplify: T /\ (F /\ a = b \/ x = y)
    result: x = y
    |}];;
