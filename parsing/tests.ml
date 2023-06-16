open Ocamlfrontend
open Core
open Pretty
open Hiptypes
open Normalize

let parse_spec s = Parser.only_effect_spec Lexer.token (Lexing.from_string s)

let parse_disj_spec s =
  Parser.only_disj_effect_spec Lexer.token (Lexing.from_string s)

let parse_fn_stage s =
  let sp = parse_spec s in
  match normalise_spec sp with
  | e :: _, _ -> e.e_constr
  | _ -> failwith "failed to parse"

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
    result: Some Norm(T/\1=b, ()); ex b; Norm(emp, b)
    norm: Some ex b; Norm(1=b, b)
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
