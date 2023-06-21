open Ocamlfrontend
open Core
open Pretty
open Hiptypes
open Normalize

let parse_spec s = Parser.only_effect_spec Lexer.token (Lexing.from_string s)
let parse_pi s = Parser.only_pure_formula Lexer.token (Lexing.from_string s)

let parse_disj_spec s =
  Parser.only_disj_effect_spec Lexer.token (Lexing.from_string s)

let parse_fn_stage s =
  let sp = parse_spec s in
  match normalise_spec sp with
  | e :: _, _ -> e.e_constr
  | _ -> failwith "failed to parse"

let%expect_test "instantiation/renaming of existentials" =
  let show a = a |> string_of_disj_spec |> print_endline in

  Pretty.verifier_counter_reset ();
  Forward_rules.renamingexistientalVar
    [parse_spec {|ex a; Norm(b=1/\emp, a+1)|}]
  |> show;
  Pretty.verifier_counter_reset ();
  Forward_rules.freshen [parse_spec {|ex a; Norm(b=1/\emp, a+1)|}] |> show;
  Pretty.verifier_counter_reset ();
  Forward_rules.instantiateExistientalVar
    (normalise_spec (parse_spec {|ex a; Norm(b=1/\emp, a+1)|}))
    [("a", "b")]
  |> normalisedStagedSpec2Spec
  |> fun a ->
  [a] |> show;
  [%expect
    {|
    ex a1; Norm(b=1, a1+1)
    Norm(b=1, a1+1)
    ex b; Norm(b=1, a+1) |}]

let%expect_test "apply lemma" =
  let test ~what ~lem:(params, left, right) applied_to =
    Pretty.verifier_counter_reset ();
    let lem =
      {
        l_name = "lemma";
        l_params = params;
        l_left = parse_fn_stage left;
        l_right = parse_spec right;
      }
    in
    let original = parse_spec applied_to in
    let spec = Entail.apply_lemma lem original in
    Format.printf "%s\n%s\noriginal: %s\nresult: %s\nnorm: %s\n---@." what
      (string_of_lemma lem)
      (string_of_normalisedStagedSpec (normalise_spec original))
      (string_of_option string_of_spec spec)
      (string_of_option string_of_spec
         (spec |> Option.map normalise_spec
         |> Option.map normalisedStagedSpec2Spec))
  in
  let l_succ = (["x"], {|f(x)|}, {|Norm(emp, x+1)|}) in
  test ~what:"hello" ~lem:l_succ {|f(1)|};
  test ~what:"constructor different, no match" ~lem:l_succ {|g(1)|};
  test ~what:"lemma causes contradiction"
    ~lem:(["x"], {|f(x)|}, {|Norm(x=2/\emp, x)|})
    {|f(1)|};
  test ~what:"parameter of lemma does not appear on the right"
    ~lem:(["x"], {|f(x)|}, {|ex b; Norm(emp, b)|})
    {|f(1)|};
  test ~what:"prefix" ~lem:l_succ {|g(2); f(1)|};
  test ~what:"suffix" ~lem:l_succ {|f(1); g(2)|};
  test ~what:"related suffix" ~lem:l_succ {|f(y); g(y)|};
  test ~what:"precondition in lemma (currently ignored)"
    ~lem:(["x"], {|req x=1/\emp; f(x)|}, {|Norm(emp, x)|})
    {|f(1)|};
  test ~what:"existential in lemma (currently ignored, seems wrong)"
    ~lem:(["x"], {|ex a; f(x)|}, {|Norm(a=1/\emp, x)|})
    {|f(1)|};
  test ~what:"existential in lemma involved in match (seems wrong)"
    ~lem:(["x"], {|ex a; f(a)|}, {|Norm(emp, x)|})
    {|f(1)|};
  test ~what:"existential and extra state in lemma (fix existential first)"
    ~lem:(["x"], {|ex a; Norm(a=3/\emp, ()); f(a)|}, {|Norm(emp, x)|})
    {|f(1)|};
  test ~what:"extra state to be matched" ~lem:l_succ {|Norm(b=2/\emp, 2); f(1)|};
  test ~what:"extra precondition to be matched" ~lem:l_succ
    {|req b=2/\emp; Norm(emp, 2); f(1)|};
  test ~what:"difficult unification"
    ~lem:(["x"], {|f(x+1)|}, {|Norm(emp, x+2)|})
    {|f(1)|};
  test ~what:"normal stage at the end is actually not matched"
    ~lem:(["x"], {|f(x); Norm(emp, 3)|}, {|Norm(emp, x+1)|})
    {|f(1)|};
  test ~what:"map"
    ~lem:(["x"], {|ex r; f(r)|}, {|Norm(emp, x)|})
    {|ex a; Norm(a=b/\b=2/\emp, 3); f(1); ex r; Norm(r=a+4/\emp, r)|};
  [%expect
    {|
    hello
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x+1, ()); Norm(emp, x+1)
    norm: Some Norm(1=x+1, x+1)
    ---
    constructor different, no match
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req emp; g$(emp, (), 1); req emp; Norm(emp, 1)
    result: None
    norm: None
    ---
    lemma causes contradiction
    lemma: forall [x], f <: Norm(x=2, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x, ()); Norm(x=2, x)
    norm: Some Norm(1=x/\x=2, x)
    ---
    parameter of lemma does not appear on the right
    lemma: forall [x], f <: ex b; Norm(emp, b)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=b2, ()); ex b2; Norm(emp, b2)
    norm: Some ex b2; Norm(1=b2, b2)
    ---
    prefix
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req emp; g$(emp, (), 2); req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some g$(emp, (), 2); Norm(T/\1=x+1, ()); Norm(emp, x+1)
    norm: Some g$(emp, (), 2); Norm(1=x+1, x+1)
    ---
    suffix
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req emp; f$(emp, (), 1); req emp; g$(emp, (), 2); req emp; Norm(emp, 2)
    result: Some Norm(T/\1=x+1, ()); Norm(emp, x+1); g$(emp, (), 2)
    norm: Some g$(1=x+1, (), 2); Norm(emp, 2)
    ---
    related suffix
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req emp; f$(emp, (), y); req emp; g$(emp, (), y); req emp; Norm(emp, y)
    result: Some Norm(T/\y=x+1, ()); Norm(emp, x+1); g$(emp, (), y)
    norm: Some g$(y=x+1, (), y); Norm(emp, y)
    ---
    precondition in lemma (currently ignored)
    lemma: forall [x], f <: Norm(emp, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x, ()); Norm(emp, x)
    norm: Some Norm(1=x, x)
    ---
    existential in lemma (currently ignored, seems wrong)
    lemma: forall [x], f <: Norm(a=1, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x, ()); Norm(a=1, x)
    norm: Some Norm(1=x/\a=1, x)
    ---
    existential in lemma involved in match (seems wrong)
    lemma: forall [x], f <: Norm(emp, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x, ()); Norm(emp, x)
    norm: Some Norm(1=x, x)
    ---
    existential and extra state in lemma (fix existential first)
    lemma: forall [x], f <: Norm(emp, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x, ()); Norm(emp, x)
    norm: Some Norm(1=x, x)
    ---
    extra state to be matched
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req emp; f$(b=2, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(b=2, 2); Norm(T/\1=x+1, ()); Norm(emp, x+1)
    norm: Some Norm(b=2/\1=x+1, x+1)
    ---
    extra precondition to be matched
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req b=2; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some req b=2; Norm(emp, 2); Norm(T/\1=x+1, ()); Norm(emp, x+1)
    norm: Some req b=2; Norm(1=x+1, x+1)
    ---
    difficult unification
    lemma: forall [x], f <: Norm(emp, x+2)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x+2, ()); Norm(emp, x+2)
    norm: Some Norm(1=x+2, x+2)
    ---
    normal stage at the end is actually not matched
    lemma: forall [x], f <: Norm(emp, x+1)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: Some Norm(T/\1=x+1, ()); Norm(emp, x+1)
    norm: Some Norm(1=x+1, x+1)
    ---
    map
    lemma: forall [x], f <: Norm(emp, x)
    original: ex a; req emp; f$(a=b/\b=2, (), 1); ex r; req emp; Norm(r=a+4, r)
    result: Some ex a; Norm(a=b/\b=2, 3); Norm(T/\1=x, ()); Norm(emp, x); ex r; Norm(r=a+4, r)
    norm: Some ex a r; Norm(a=b/\b=2/\1=x/\r=a+4, r)
    --- |}]

let%expect_test "normalise spec" =
  verifier_counter_reset ();
  let test s =
    let n = normalise_spec s in
    Format.printf "%s\n==>\n%s\n@." (string_of_spec s)
      (string_of_normalisedStagedSpec n)
  in
  print_endline "--- norm\n";
  test
    [
      NormalReturn (True, PointsTo ("x", Num 2), UNIT);
      Require (True, PointsTo ("x", Num 1));
    ];
  test
    [
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      Require (True, PointsTo ("y", Num 2));
      NormalReturn (True, PointsTo ("y", Num 2), UNIT);
    ];
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), UNIT);
    ];
  test
    [
      NormalReturn
        (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2)), UNIT);
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), UNIT);
    ];
  test
    [
      NormalReturn (Atomic (EQ, Var "a", Num 3), PointsTo ("y", Var "a"), UNIT);
      Require (Atomic (EQ, Var "b", Var "a"), PointsTo ("x", Var "b"));
      NormalReturn (True, PointsTo ("x", Plus (Var "b", Num 1)), UNIT);
    ];
  print_endline "--- existential locations\n";
  test
    [
      Exists ["x"];
      NormalReturn (Atomic (EQ, Var "x", Var "y"), PointsTo ("x", Num 1), UNIT);
      Exists ["y"];
      Require (True, PointsTo ("y", Num 1));
    ];
  test
    [
      Exists ["x"];
      NormalReturn (Atomic (EQ, Var "x", Var "y"), PointsTo ("x", Num 2), UNIT);
      Exists ["y"];
      Require (True, PointsTo ("y", Num 1));
    ];
  test
    [
      Exists ["x"];
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      Exists ["y"];
      Require (True, PointsTo ("y", Num 1));
      NormalReturn (Atomic (EQ, Var "x", Var "y"), EmptyHeap, UNIT);
    ];
  print_endline "--- eff\n";
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      Require (True, PointsTo ("x", Var "1"));
      RaisingEff (True, PointsTo ("x", Num 1), ("E", [Num 3]), UNIT);
      NormalReturn (True, PointsTo ("y", Num 2), UNIT);
    ];
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      HigherOrder (True, EmptyHeap, ("f", [Num 3]), UNIT);
      NormalReturn (True, PointsTo ("y", Num 2), UNIT);
    ];
  [%expect
    {|
  --- norm

  Norm(x->2, ()); req x->1
  ==>
  req F; Norm(F, ())

  req x->1; Norm(x->1, ()); req y->2; Norm(y->2, ())
  ==>
  req x->1*y->2; Norm(x->1*y->2, ())

  Norm(x->1, ()); req x->a; Norm(x->a+1, ())
  ==>
  req 1=a; Norm(x->a+1 /\ a=1, ())

  Norm(x->1*y->2, ()); req x->a; Norm(x->a+1, ())
  ==>
  req 1=a; Norm(y->2*x->a+1 /\ a=1, ())

  Norm(y->a /\ a=3, ()); req x->b /\ b=a; Norm(x->b+1, ())
  ==>
  req x->b /\ b=a; Norm(y->a*x->b+1 /\ a=3, ())

  --- existential locations

  ex x; Norm(x->1 /\ x=y, ()); ex y; req y->1
  ==>
  ex x; req emp; Norm(x=x, ())

  ex x; Norm(x->2 /\ x=y, ()); ex y; req y->1
  ==>
  ex x; req F; Norm(x=x/\F, ())

  ex x; Norm(x->1, ()); ex y; req y->1; Norm(x=y, ())
  ==>
  ex x; req emp; Norm(x=x, ())

  --- eff

  Norm(x->1, ()); req x->1; E(x->1, (3), ()); Norm(y->2, ())
  ==>
  req 1=1; E(x->1 /\ 1=1, (3), ()); req emp; Norm(y->2, ())

  Norm(x->1, ()); f$(emp, (3), ()); Norm(y->2, ())
  ==>
  req emp; f$(x->1, (3), ()); req emp; Norm(y->2, ())
|}]

let entails_pure env s1 vars s2 =
  Provers.entails_exists
    (SMap.of_seq (List.to_seq env))
    (parse_pi s1) vars (parse_pi s2)

let%expect_test _ =
  Format.printf "%b@."
    (entails_pure
       [("x16", Int); ("xs", List_int); ("xs17", List_int); ("xs37", List_int)]
       {|head(xs)=x16/\tail(xs)=xs17/\is_cons(xs)=true/\_f18=1+x16+r|} ["xs37"]
       {|r=_f35/\xs17=xs37/\head(xs)=x36/\tail(xs)=xs37/\is_cons(xs)=true|});
  [%expect {| false |}]
