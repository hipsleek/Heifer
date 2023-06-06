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
      (string_of_lemma lem) (string_of_spec original) (string_of_spec spec)
      (string_of_spec (normalisedStagedSpec2Spec (normalise_spec spec)))
  in
  test ~what:"hello"
    ~lem:(["x"], {|f(x)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(1)|};
  test ~what:"prefix"
    ~lem:(["x"], {|f(x)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|g(2); f(1)|};
  test ~what:"suffix"
    ~lem:(["x"], {|f(x)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(1); g(2)|};
  test ~what:"related suffix"
    ~lem:(["x"], {|f(x)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(x); g(x)|};
  test ~what:"precondition in lemma (currently ignored)"
    ~lem:(["x"], {|ex a; req x=1/\emp; f(x)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(1)|};
  test ~what:"existential in lemma (currently ignored)"
    ~lem:(["x"], {|ex a; f(a)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(1)|};
  test ~what:"extra state in lemma"
    ~lem:(["x"], {|ex a; Norm(a=3/\emp, ()); f(a)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(1)|};
  test ~what:"constructor different"
    ~lem:(["x"], {|f(x)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|g(1)|};
  test ~what:"non-param in lemma"
    ~lem:(["y"], {|f(x)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(1)|};
  test ~what:"difficult unification"
    ~lem:(["x"], {|f(x+1)|}, {|ex b; Norm(b=2/\emp, b)|})
    {|f(1)|};
  [%expect
    {|
    hello
    lemma: forall [x], f$(emp, [], x) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], 1)
    result: ex ; Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); Norm(emp, 1)
    norm: ex b_1; Norm(b_1=1/\b_1=2, 1)
    ---
    prefix
    lemma: forall [x], f$(emp, [], x) ==> ex b; Norm(b=2, b)
    original: g$(emp, [], 2); f$(emp, [], 1)
    result: g$(emp, [], 2); Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); f$(emp, [], 1); Norm(emp, 1)
    norm: g$(emp, [], 2); ex b_1; f$(b_1=1/\b_1=2, [], 1); Norm(emp, 1)
    ---
    suffix
    lemma: forall [x], f$(emp, [], x) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], 1); g$(emp, [], 2)
    result: ex ; Norm(emp, ()); Norm(b_1=2, ()); ex b_1; Norm(b_1=2, b_1); g$(emp, [], 2); Norm(emp, 2)
    norm: ex b_1; g$(b_1=2/\b_1=2, [], 2); Norm(emp, 2)
    ---
    related suffix
    lemma: forall [x], f$(emp, [], x) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], x); g$(emp, [], x)
    result: ex ; Norm(emp, ()); Norm(b_1=x, ()); ex b_1; Norm(b_1=2, b_1); g$(emp, [], x); Norm(emp, x)
    norm: ex b_1; g$(b_1=x/\b_1=2, [], x); Norm(emp, x)
    ---
    precondition in lemma (currently ignored)
    lemma: forall [x], ex a; req x=1; f$(emp, [], x) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], 1)
    result: ex ; Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); Norm(emp, 1)
    norm: ex b_1; Norm(b_1=1/\b_1=2, 1)
    ---
    existential in lemma (currently ignored)
    lemma: forall [x], ex a; f$(emp, [], a) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], 1)
    result: ex ; Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); Norm(emp, 1)
    norm: ex b_1; Norm(b_1=1/\b_1=2, 1)
    ---
    extra state in lemma
    lemma: forall [x], ex a; Norm(a=3, ()); f$(emp, [], a) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], 1)
    result: ex ; Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); Norm(emp, 1)
    norm: ex b_1; Norm(b_1=1/\b_1=2, 1)
    ---
    constructor different
    lemma: forall [x], f$(emp, [], x) ==> ex b; Norm(b=2, b)
    original: g$(emp, [], 1)
    result: g$(emp, [], 1); Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); Norm(emp, 1)
    norm: g$(emp, [], 1); ex b_1; Norm(b_1=1/\b_1=2, 1)
    ---
    non-param in lemma
    lemma: forall [y], f$(emp, [], x) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], 1)
    result: ex ; Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); Norm(emp, 1)
    norm: ex b_1; Norm(b_1=1/\b_1=2, 1)
    ---
    difficult unification
    lemma: forall [x], f$(emp, [], x+1) ==> ex b; Norm(b=2, b)
    original: f$(emp, [], 1)
    result: ex ; Norm(emp, ()); Norm(b_1=1, ()); ex b_1; Norm(b_1=2, b_1); Norm(emp, 1)
    norm: ex b_1; Norm(b_1=1/\b_1=2, 1)
    --- |}]
