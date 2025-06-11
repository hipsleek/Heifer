open Hipcore
open Hiptypes
open Rewriting

let term_add_folding_rules = 
  let num_constant_folding_rule op f =
    (* currently, directly matching on the contents of a term is not supported,
       so we use this workaround for now *)
    let open Rules.Term in
    dynamic_rule (BinOp (op, uvar "a", uvar "b"))
      (fun sub ->
        let a, b = of_uterm (sub "a"), of_uterm (sub "b") in
        match a, b with
        | Const (Num a), Const (Num b) -> Const (Num (f a b))
        | a, b -> BinOp (op, a, b)
      )
  in
  [ 
  num_constant_folding_rule Plus (+);
  num_constant_folding_rule Minus (-);
  num_constant_folding_rule TTimes ( * );
  num_constant_folding_rule TDiv (/);
]

let simplify_term (t : term) = 
  let database =
    term_add_folding_rules
  in
  autorewrite database (Term t) |> Rules.Term.of_uterm

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

let pure_eq_not_distribute_rules = Rules.(Pure.[
  rule (Not (Atomic (EQ, Term.uvar "t", Const TTrue))) (Atomic (EQ, Term.uvar "t", Const TFalse));
  rule (Not (Atomic (EQ, Term.uvar "t", Const TFalse))) (Atomic (EQ, Term.uvar "t", Const TTrue));
])

let simplify_pure (p : pi) =
  let database = 
    pure_and_folding_rules
    @ pure_or_folding_rules
    @ pure_not_folding_rules
    @ pure_eq_not_distribute_rules
  in
  autorewrite database (Pure p) |> Rules.Pure.of_uterm

let kappa_emp_folding_rules = Rules.Heap.[
  rule (SepConj (EmptyHeap, (uvar "k"))) (uvar "k");
  rule (SepConj (uvar "k", EmptyHeap)) (uvar "k")]

let simplify_kappa (h : kappa) =
  autorewrite kappa_emp_folding_rules (Heap h) |> Rules.Heap.of_uterm

let%expect_test "simplify tests" =
  let test simpl printer v =
    Format.printf "simplify: %s@." (printer v);
    Format.printf "result: %s@." (printer (simpl v))
  in
  let h1 =  (SepConj (EmptyHeap, SepConj (PointsTo ("x", Const (Num 1)), EmptyHeap))) in
  test simplify_kappa Pretty.string_of_kappa h1;
  [%expect {|
    simplify: emp*x->1*emp
    result: x->1
    |}];

  let t = BinOp (TTimes, Const (Num 5), BinOp (Plus, Const (Num 6), BinOp (Minus, Const (Num 10), Const (Num 3)))) in
  test simplify_term Pretty.string_of_term t;
  [%expect {|
    simplify: (5 * (6 + (10 - 3)))
    result: 65
    |}];

  let p1 = And (True, Or ( And (False, Atomic (EQ, Var "a", Var "b")), Atomic (EQ, Var "x", Var "y"))) in
  test simplify_pure Pretty.string_of_pi p1;
  [%expect {|
    simplify: T/\F/\a=b\/x=y
    result: x=y
    |}];;
