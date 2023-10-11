open Ocamlfrontend
open Hipcore
open Hipprover
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
    ex v1; Norm(res=v1+1/\b=1)
    Norm(res=v1+1/\b=1)
    ex b; Norm(res=a+1/\b=1) |}]

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
  let l_succ = (["x"], {|f(x)|}, {|ens res=x+1|}) in
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
    lemma: forall [x], f <: Norm(res=x+1)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x+1); Norm(res=x+1)
    norm: Some Norm(1=x+1/\res=x+1)
    ---
    constructor different, no match
    lemma: forall [x], f <: Norm(res=x+1)
    original: req emp; g(, 1); req emp; Norm(res=1)
    result: None
    norm: None
    ---
    lemma causes contradiction
    lemma: forall [x], f <: Norm(res=x/\x=2)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x); Norm(res=x/\x=2)
    norm: Some Norm(1=x/\res=x/\x=2)
    ---
    parameter of lemma does not appear on the right
    lemma: forall [x], f <: ex b; Norm(res=b/\T)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=v2); ex v2; Norm(res=v2)
    norm: Some ex v2; Norm(1=v2/\res=v2)
    ---
    prefix
    lemma: forall [x], f <: Norm(res=x+1)
    original: req emp; g(, 2); req emp; f(, 1); req emp; Norm(res=1)
    result: Some g(, 2); Norm(T/\1=x+1); Norm(res=x+1)
    norm: Some g(, 2); Norm(1=x+1/\res=x+1)
    ---
    suffix
    lemma: forall [x], f <: Norm(res=x+1)
    original: req emp; f(, 1); req emp; g(, 2); req emp; Norm(res=2)
    result: Some Norm(T/\1=x+1); Norm(res=x+1); g(, 2)
    norm: Some ens 1=x+1; g(, 2); Norm(res=2)
    ---
    related suffix
    lemma: forall [x], f <: Norm(res=x+1)
    original: req emp; f(, y); req emp; g(, y); req emp; Norm(res=y)
    result: Some Norm(T/\y=x+1); Norm(res=x+1); g(, y)
    norm: Some ens y=x+1; g(, y); Norm(res=y)
    ---
    precondition in lemma (currently ignored)
    lemma: forall [x], f <: Norm(res=x/\T)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x); Norm(res=x)
    norm: Some Norm(1=x/\res=x)
    ---
    existential in lemma (currently ignored, seems wrong)
    lemma: forall [x], f <: Norm(res=x/\a=1)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x); Norm(res=x/\a=1)
    norm: Some Norm(1=x/\res=x/\a=1)
    ---
    existential in lemma involved in match (seems wrong)
    lemma: forall [x], f <: Norm(res=x/\T)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x); Norm(res=x)
    norm: Some Norm(1=x/\res=x)
    ---
    existential and extra state in lemma (fix existential first)
    lemma: forall [x], f <: Norm(res=x/\T)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x); Norm(res=x)
    norm: Some Norm(1=x/\res=x)
    ---
    extra state to be matched
    lemma: forall [x], f <: Norm(res=x+1)
    original: req emp; ens b=2; f(, 1); req emp; Norm(res=1)
    result: Some Norm(res=2/\b=2); Norm(T/\1=x+1); Norm(res=x+1)
    norm: Some Norm(b=2/\1=x+1/\res=x+1)
    ---
    extra precondition to be matched
    lemma: forall [x], f <: Norm(res=x+1)
    original: req b=2; f(, 1); req emp; Norm(res=1)
    result: Some req b=2; Norm(res=2/\T); Norm(T/\1=x+1); Norm(res=x+1)
    norm: Some req b=2; Norm(1=x+1/\res=x+1)
    ---
    difficult unification
    lemma: forall [x], f <: Norm(res=x+2/\T)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x+2); Norm(res=x+2)
    norm: Some Norm(1=x+2/\res=x+2)
    ---
    normal stage at the end is actually not matched
    lemma: forall [x], f <: Norm(res=x+1/\T)
    original: req emp; f(, 1); req emp; Norm(res=1)
    result: Some Norm(T/\1=x+1); Norm(res=x+1)
    norm: Some Norm(1=x+1/\res=x+1)
    ---
    map
    lemma: forall [x], f <: Norm(res=x/\T)
    original: ex a; req emp; ens a=b/\b=2; f(, 1); ex r; req emp; Norm(res=r/\r=a+4)
    result: Some ex a; Norm(res=3/\a=b/\b=2); Norm(T/\1=x); Norm(res=x); ex r; Norm(res=r/\r=a+4)
    norm: Some ex a r; Norm(a=b/\b=2/\1=x/\res=r/\r=a+4)
    --- |}]

let%expect_test "normalise spec" =
  verifier_counter_reset ();
  let test s =
    try
      let n = normalise_spec s in
      Format.printf "%s\n==>\n%s\n@." (string_of_spec s)
        (string_of_normalisedStagedSpec n)
    with Norm_failure -> Format.printf "%s\n=/=>\n@." (string_of_spec s)
  in
  print_endline "--- norm\n";
  test
    [
      NormalReturn (True, PointsTo ("x", Num 2));
      Require (True, PointsTo ("x", Num 1));
    ];
  test
    [
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 1));
      Require (True, PointsTo ("y", Num 2));
      NormalReturn (True, PointsTo ("y", Num 2));
    ];
  test
    [
      Exists ["a"];
      NormalReturn (True, PointsTo ("x", Num 1));
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)));
    ];
  test
    [
      Exists ["a"];
      NormalReturn (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2)));
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)));
    ];
  test
    [
      Exists ["a"];
      NormalReturn (Atomic (EQ, Var "a", Num 3), PointsTo ("y", Var "a"));
      Require (Atomic (EQ, Var "b", Var "a"), PointsTo ("x", Var "b"));
      NormalReturn (True, PointsTo ("x", Plus (Var "b", Num 1)));
    ];
  print_endline "--- existential locations\n";
  test
    [
      Exists ["x"];
      NormalReturn (Atomic (EQ, Var "x", Var "y"), PointsTo ("x", Num 1));
      Exists ["y"];
      Require (True, PointsTo ("y", Num 1));
    ];
  test
    [
      Exists ["x"];
      NormalReturn (Atomic (EQ, Var "x", Var "y"), PointsTo ("x", Num 2));
      Exists ["y"];
      Require (True, PointsTo ("y", Num 1));
    ];
  test
    [
      Exists ["x"];
      NormalReturn (True, PointsTo ("x", Num 1));
      Exists ["y"];
      Require (True, PointsTo ("y", Num 1));
      NormalReturn (Atomic (EQ, Var "x", Var "y"), EmptyHeap);
    ];
  print_endline "--- eff\n";
  (* not sure why this is false, and also if it can appear in a real program *)
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1));
      Require (True, PointsTo ("x", Var "1"));
      RaisingEff (True, PointsTo ("x", Num 1), ("E", [Num 3]), UNIT);
      NormalReturn (True, PointsTo ("y", Num 2));
    ];
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1));
      HigherOrder (True, EmptyHeap, ("f", [Num 3]), UNIT);
      NormalReturn (True, PointsTo ("y", Num 2));
    ];
  [%expect
    {|
  --- norm

  Norm(x->2); req x->1
  =/=>

  req x->1; Norm(x->1); req y->2; Norm(y->2)
  ==>
  req x->1*y->2; Norm(x->1*y->2)

  ex a; Norm(x->1); req x->a; Norm(x->a+1)
  ==>
  ex a; req 1=a; Norm(x->a+1 /\ a=1)

  ex a; Norm(x->1*y->2); req x->a; Norm(x->a+1)
  ==>
  ex a; req 1=a; Norm(y->2*x->a+1 /\ a=1)

  ex a; Norm(y->a /\ a=3); req x->b /\ b=a; Norm(x->b+1)
  ==>
  ex a; req x->b /\ b=a; Norm(y->a*x->b+1 /\ a=3)

  --- existential locations

  ex x; Norm(x->1 /\ x=y); ex y; req y->1
  ==>
  ex x; req emp; Norm(x=x)

  ex x; Norm(x->2 /\ x=y); ex y; req y->1
  =/=>

  ex x; Norm(x->1); ex y; req y->1; Norm(x=y)
  ==>
  ex x; req emp; Norm(x=x)

  --- eff

  Norm(x->1); req x->1; E(x->1, (3), ()); Norm(y->2)
  =/=>

  Norm(x->1); f(3, ()); Norm(y->2)
  ==>
  req emp; ens x->1; f(3, ()); req emp; Norm(y->2)
|}]

let entails_pure env_a s1 vars s2 =
  let s1 = parse_pi s1 in
  let s2 = parse_pi s2 in
  let env = create_abs_env () in
  let env = Infer_types.infer_types_pi env s1 in
  let env = Infer_types.infer_types_pi env s2 in
  let env = Infer_types.concrete_type_env env in
  let env = SMap.add_seq (List.to_seq env_a) env in
  Provers.entails_exists env s1 vars s2

let%expect_test _ =
  Format.printf "%b@."
    (entails_pure []
       {|head(xs)=x16/\tail(xs)=xs17/\is_cons(xs)=true/\_f18=1+x16+r|} ["xs37"]
       {|r=_f35/\xs17=xs37/\head(xs)=x36/\tail(xs)=xs37/\is_cons(xs)=true|});
  [%expect {| false |}]
