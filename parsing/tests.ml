open Ocamlfrontend
open Core
open Pretty
open Hiptypes
open Normalize

let parse_spec s = Parser.only_effect_spec Lexer.token (Lexing.from_string s)

let parse_disj_spec s =
  Parser.only_disj_effect_spec Lexer.token (Lexing.from_string s)

let%expect_test "existentials" =
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
    ex a_1; Norm(b=1, a_1+1)
    Norm(b=1, a_1+1)
    ex b; Norm(b=1, a+1) |}]

let%expect_test "apply lemma" =
  let test ~what ~lem:(params, left, right) applied_to =
    Pretty.verifier_counter_reset ();
    let lem =
      {
        l_name = "lemma";
        l_params = params;
        l_left = parse_spec left;
        l_right = parse_spec right;
      }
    in
    let original = parse_spec applied_to in
    let spec = Entail.apply_lemma lem original in
    Format.printf "%s\n%s\noriginal: %s\nresult: %s\nnorm: %s\n---@." what
      (string_of_lemma lem)
      (string_of_normalisedStagedSpec (normalise_spec original))
      (string_of_spec spec)
      (string_of_spec (normalisedStagedSpec2Spec (normalise_spec spec)))
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
    lemma: forall [x], f$(emp, (), x) ==> Norm(emp, x+1)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(emp, 1+1)
    norm: Norm(emp, 1+1)
    ---
    constructor different, no match
    lemma: forall [x], f$(emp, (), x) ==> Norm(emp, x+1)
    original: req emp; g$(emp, (), 1); req emp; Norm(emp, 1)
    result: g$(emp, (), 1)
    norm: g$(emp, (), 1); Norm(emp, 1)
    ---
    lemma causes contradiction
    lemma: forall [x], f$(emp, (), x) ==> Norm(x=2, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(1=2, 1)
    norm: Norm(1=2, 1)
    ---
    parameter of lemma does not appear on the right
    lemma: forall [x], f$(emp, (), x) ==> ex b; Norm(emp, b)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); ex b_1; Norm(emp, b_1)
    norm: ex b_1; Norm(emp, b_1)
    ---
    prefix
    lemma: forall [x], f$(emp, (), x) ==> Norm(emp, x+1)
    original: req emp; g$(emp, (), 2); req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: g$(emp, (), 2); Norm(emp, ()); ex ; Norm(emp, ()); Norm(emp, 1+1)
    norm: g$(emp, (), 2); Norm(emp, 1+1)
    ---
    suffix
    lemma: forall [x], f$(emp, (), x) ==> Norm(emp, x+1)
    original: req emp; f$(emp, (), 1); req emp; g$(emp, (), 2); req emp; Norm(emp, 2)
    result: ex ; Norm(emp, ()); Norm(emp, 1+1); g$(emp, (), 2); Norm(emp, 2)
    norm: g$(emp, (), 2); Norm(emp, 2)
    ---
    related suffix
    lemma: forall [x], f$(emp, (), x) ==> Norm(emp, x+1)
    original: req emp; f$(emp, (), y); req emp; g$(emp, (), y); req emp; Norm(emp, y)
    result: ex ; Norm(emp, ()); Norm(emp, y+1); g$(emp, (), y); Norm(emp, y)
    norm: g$(emp, (), y); Norm(emp, y)
    ---
    precondition in lemma (currently ignored)
    lemma: forall [x], req x=1; f$(emp, (), x) ==> Norm(emp, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(emp, 1)
    norm: Norm(emp, 1)
    ---
    existential in lemma (currently ignored, seems wrong)
    lemma: forall [x], ex a; f$(emp, (), x) ==> Norm(a=1, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(a=1, 1)
    norm: Norm(a=1, 1)
    ---
    existential in lemma involved in match (seems wrong)
    lemma: forall [x], ex a; f$(emp, (), a) ==> Norm(emp, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(emp, x)
    norm: Norm(emp, x)
    ---
    existential and extra state in lemma (fix existential first)
    lemma: forall [x], ex a; Norm(a=3, ()); f$(emp, (), a) ==> Norm(emp, x)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(emp, x)
    norm: Norm(emp, x)
    ---
    extra state to be matched
    lemma: forall [x], f$(emp, (), x) ==> Norm(emp, x+1)
    original: req emp; f$(b=2, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(b=2, ()); Norm(emp, 1+1)
    norm: Norm(b=2, 1+1)
    ---
    extra precondition to be matched
    lemma: forall [x], f$(emp, (), x) ==> Norm(emp, x+1)
    original: req b=2; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(emp, 1+1)
    norm: Norm(emp, 1+1)
    ---
    difficult unification
    lemma: forall [x], f$(emp, (), x+1) ==> Norm(emp, x+2)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(emp, x+2)
    norm: Norm(emp, x+2)
    ---
    normal stage at the end is actually not matched
    lemma: forall [x], f$(emp, (), x); Norm(emp, 3) ==> Norm(emp, x+1)
    original: req emp; f$(emp, (), 1); req emp; Norm(emp, 1)
    result: ex ; Norm(emp, ()); Norm(emp, 1+1)
    norm: Norm(emp, 1+1)
    ---
    map
    lemma: forall [x], ex r; f$(emp, (), r) ==> Norm(emp, x)
    original: ex a; req emp; f$(a=b/\b=2, (), 1); ex r; req emp; Norm(r=a+4, r)
    result: ex a; Norm(a=b/\b=2, ()); Norm(emp, x)
    norm: ex a; Norm(a=b/\b=2, x)
    --- |}]
