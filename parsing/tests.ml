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

let%expect_test "instantiation/renaming of existentials" =
  let show a = a |> string_of_disj_spec |> print_endline in

  Pretty.verifier_counter_reset ();
  (* renames existentials *)
  Forward_rules.renamingexistientalVar
    [parse_spec {|ex a; Norm(b=1/\emp, a+1)|}]
  |> show;
  Pretty.verifier_counter_reset ();
  (* renames, then removes *)
  Forward_rules.freshen [parse_spec {|ex a; Norm(b=1/\emp, a+1)|}] |> show;
  Pretty.verifier_counter_reset ();
  (* renames only existentials without regard for binding and could change meaning, so only rename after ensuring freshness *)
  Forward_rules.instantiateExistientalVar
    (normalize_spec (parse_spec {|ex a; Norm(b=1/\emp, a+1)|}))
    [("a", "b")]
  |> normalisedStagedSpec2Spec
  |> fun a ->
  [a] |> show;
  [%expect
    {|
    ex v0; ens res=v0+1/\b=1
    ens res=v0+1/\b=1
    ex b; ens res=a+1/\b=1 |}]

let%expect_test "apply lemma" =
  let test ~what ~lem:(params, left, right) applied_to =
    Pretty.verifier_counter_reset ();
    let parse_fn_stage_as_lem_lhs s =
      let sp = parse_spec s in
      match normalize_spec sp with
      | EffHOStage e :: _, _ ->
        let f, a = e.e_constr in
        (f, a @ [e.e_ret])
      | _ -> failwith "failed to parse"
    in
    let lem =
      {
        l_name = "lemma";
        l_params = params;
        l_left = parse_fn_stage_as_lem_lhs left;
        l_right = parse_spec right;
      }
    in
    let original = parse_spec applied_to in
    let spec = Entail.apply_lemma lem original in
    Format.printf "%s\n%s\noriginal: %s\nresult: %s\nnorm: %s\n---@." what
      (string_of_lemma lem)
      (string_of_normalisedStagedSpec (normalize_spec original))
      (string_of_option string_of_spec spec)
      (string_of_option string_of_spec
         (spec |> Option.map normalize_spec
         |> Option.map normalisedStagedSpec2Spec))
  in
  let l_succ = (["x"; "res"], {|f(x, res)|}, {|ens res=x+1|}) in
  test ~what:"hello" ~lem:l_succ {|f(1, 2)|};
  test ~what:"constructor different, no match" ~lem:l_succ {|g(1, 2)|};
  test ~what:"lemma causes contradiction"
    ~lem:(["x"; "res"], {|f(x, res)|}, {|Norm(x=2/\emp, x)|})
    {|f(1,2)|};
  test ~what:"parameter of lemma does not appear on the right"
    ~lem:(["x"; "res"], {|f(x, res)|}, {|ex b; Norm(emp, b)|})
    {|f(1,2)|};
  test ~what:"prefix" ~lem:l_succ {|g(2); f(1, 3)|};
  test ~what:"suffix" ~lem:l_succ {|f(1, 3); g(2)|};
  test ~what:"related suffix" ~lem:l_succ {|f(y, z); g(y)|};
  test ~what:"precondition in lemma (currently ignored)"
    ~lem:(["x"; "res"], {|req x=1/\emp; f(x,res)|}, {|Norm(emp, x)|})
    {|f(1,2)|};
  test ~what:"existential in lemma (currently ignored, seems wrong)"
    ~lem:(["x"; "res"], {|ex a; f(x,res)|}, {|Norm(a=1/\emp, x)|})
    {|f(1,2)|};
  test ~what:"existential in lemma involved in match (seems wrong)"
    ~lem:(["x"; "res"], {|ex a; f(a,res)|}, {|Norm(emp, x)|})
    {|f(1,2)|};
  test ~what:"existential and extra state in lemma (fix existential first)"
    ~lem:(["x"; "res"], {|ex a; Norm(a=3/\emp, ()); f(a,res)|}, {|Norm(emp, x)|})
    {|f(1,2)|};
  test ~what:"extra state to be matched" ~lem:l_succ
    {|Norm(b=2/\emp, 2); f(1, 2)|};
  test ~what:"extra precondition to be matched" ~lem:l_succ
    {|req b=2/\emp; Norm(emp, 2); f(1, 2)|};
  test ~what:"difficult unification"
    ~lem:(["x"; "res"], {|f(x+1,res)|}, {|Norm(emp, x+2)|})
    {|f(1,2)|};
  test ~what:"normal stage at the end is actually not matched"
    ~lem:(["x"; "res"], {|f(x, res); Norm(emp, 3)|}, {|Norm(emp, x+1)|})
    {|f(1,2)|};
  test ~what:"map"
    ~lem:(["x"; "res"], {|f(x,res)|}, {|Norm(emp, x)|})
    {|ex a; Norm(a=b/\b=2/\emp, 3); f(1, 2); ex r; Norm(r=a+4/\emp, r)|};
  [%expect
    {|
    hello
    lemma: forall [x; res], f(x,res) <: ens res=x+1
    original: req emp; f(1, 2); req emp; ens emp
    result: Some ens T/\T; ens 2=1+1
    norm: Some ens emp
    ---
    constructor different, no match
    lemma: forall [x; res], f(x,res) <: ens res=x+1
    original: req emp; g(1, 2); req emp; ens emp
    result: None
    norm: None
    ---
    lemma causes contradiction
    lemma: forall [x; res], f(x,res) <: ens res=x/\x=2
    original: req emp; f(1, 2); req emp; ens emp
    result: Some ens T/\T; ens 2=1/\1=2
    norm: Some ens 2=1/\1=2
    ---
    parameter of lemma does not appear on the right
    lemma: forall [x; res], f(x,res) <: ex b; ens res=b/\T
    original: req emp; f(1, 2); req emp; ens emp
    result: Some ens T/\T; ex v0; ens 2=v0
    norm: Some ens emp
    ---
    prefix
    lemma: forall [x; res], f(x,res) <: ens res=x+1
    original: req emp; g(2); req emp; f(1, 3); req emp; ens emp
    result: Some g(2); ens T/\T; ens 3=1+1
    norm: Some g(2); ens 3=2
    ---
    suffix
    lemma: forall [x; res], f(x,res) <: ens res=x+1
    original: req emp; f(1, 3); req emp; g(2); req emp; ens emp
    result: Some ens T/\T; ens 3=1+1; g(2)
    norm: Some ens F
    ---
    related suffix
    lemma: forall [x; res], f(x,res) <: ens res=x+1
    original: req emp; f(y, z); req emp; g(y); req emp; ens emp
    result: Some ens T/\T; ens z=y+1; g(y)
    norm: Some ens z=y+1; g(y); ens emp
    ---
    precondition in lemma (currently ignored)
    lemma: forall [x; res], f(x,res) <: ens res=x/\T
    original: req emp; f(1, 2); req emp; ens emp
    result: Some ens T/\T; ens 2=1
    norm: Some ens 2=1
    ---
    existential in lemma (currently ignored, seems wrong)
    lemma: forall [x; res], f(x,res) <: ens res=x/\a=1
    original: req emp; f(1, 2); req emp; ens emp
    result: Some ens T/\T; ens 2=1/\a=1
    norm: Some ens 2=1/\a=1
    ---
    existential in lemma involved in match (seems wrong)
    lemma: forall [x; res], f(a,res) <: ens res=x/\T
    original: req emp; f(1, 2); req emp; ens emp
    result: None
    norm: None
    ---
    existential and extra state in lemma (fix existential first)
    lemma: forall [x; res], f(a,res) <: ens res=x/\T
    original: req emp; f(1, 2); req emp; ens emp
    result: None
    norm: None
    ---
    extra state to be matched
    lemma: forall [x; res], f(x,res) <: ens res=x+1
    original: req emp; ens b=2; f(1, 2); req emp; ens emp
    result: Some ens res=2/\b=2; ens T/\T; ens 2=1+1
    norm: Some ens res=2/\b=2
    ---
    extra precondition to be matched
    lemma: forall [x; res], f(x,res) <: ens res=x+1
    original: req b=2; f(1, 2); req emp; ens emp
    result: Some req b=2; ens res=2/\T; ens T/\T; ens 2=1+1
    norm: Some req b=2; ens res=2
    ---
    difficult unification
    lemma: forall [x; res], f(x+1,res) <: ens res=x+2/\T
    original: req emp; f(1, 2); req emp; ens emp
    result: None
    norm: None
    ---
    normal stage at the end is actually not matched
    lemma: forall [x; res], f(x,res) <: ens res=x+1/\T
    original: req emp; f(1, 2); req emp; ens emp
    result: Some ens T/\T; ens 2=1+1
    norm: Some ens emp
    ---
    map
    lemma: forall [x; res], f(x,res) <: ens res=x/\T
    original: ex a; req emp; ens a=b/\b=2; f(1, 2); ex r; req emp; ens res=a+4
    result: Some ex a; ens res=3/\a=b/\b=2; ens T/\T; ens 2=1; ex r; ens res=r/\r=a+4
    norm: Some ex a r; ens a=b/\b=2/\2=1/\res=a+4
    --- |}]

let%expect_test "normalise spec" =
  (* Debug.debug_level := 5; *)
  verifier_counter_reset ();
  let test s =
    try
      let n = normalize_spec s in
      Format.printf "%s\n==>\n%s\n@." (string_of_spec s)
        (string_of_normalisedStagedSpec n)
    with Norm_failure -> Format.printf "%s\n=/=>\n@." (string_of_spec s)
  in
  let test1 s = test (parse_spec s) in
  print_endline "--- norm\n";
  test [NormalReturn (True, EmptyHeap)];
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
  print_endline "--- regression\n";
  test1
    "ex x1; Read(emp, (), x1); ex x2; Write(emp, (x1+1), x2); ex x3; Read(emp, \
     (), x3); Norm(res=x3)";
  print_endline "--- optimization\n";
  test1 {|ex v1 v2 v3 v4; ens res=v1 /\ v1=v2 /\ v2=v3 /\ v4=v1|};
  test1 {|ex v1 v2 v3 r; f(v1, r); ens res=v1+1 /\ v2=r /\ v3=v2|};
  [%expect
    {|
  --- norm

  ens emp
  ==>
  req emp; ens emp

  ens x->2; req x->1
  =/=>

  req x->1; ens x->1; req y->2; ens y->2
  ==>
  req x->1*y->2; ens x->1*y->2

  ex a; ens x->1; req x->a; ens x->a+1
  ==>
  ex a; req 1=a; ens x->a+1/\a=1

  ex a; ens x->1*y->2; req x->a; ens x->a+1
  ==>
  ex a; req 1=a; ens y->2*x->a+1/\a=1

  ex a; ens y->a/\a=3; req x->b/\b=a; ens x->b+1
  ==>
  ex a; req x->b/\b=a; ens y->a*x->b+1/\a=3

  --- existential locations

  ex x; ens x->1/\x=y; ex y; req y->1
  ==>
  req emp; ens emp

  ex x; ens x->2/\x=y; ex y; req y->1
  =/=>

  ex x; ens x->1; ex y; req y->1; ens x=y
  ==>
  req emp; ens emp

  --- eff

  ens x->1; req x->1; E(x->1, (3), ()); ens y->2
  ==>
  req 1=1; E(x->1/\1=1, (3), ()); req emp; ens y->2/\res=()

  ens x->1; f(3, ()); ens y->2
  ==>
  req emp; ens x->1; f(3, ()); req emp; ens y->2

  --- regression

  ex x1; Read(emp, (()), x1); ex x2; Write(emp, (x1+1), x2); ex x3; Read(emp, (()), x3); ens res=x3
  ==>
  ex x1; req emp; Read(emp, (()), x1); ex x2; req emp; Write(emp, (x1+1), x2); ex x3; req emp; Read(emp, (()), x3); req emp; ens res=x3

  --- optimization

  ex v1 v2 v3 v4; ens res=v1/\v1=v2/\v2=v3/\v4=v1
  ==>
  ex v4; req emp; ens res=v4

  ex v1 v2 v3 r; f(v1, r); ens res=v1+1/\v2=r/\v3=v2
  ==>
  ex v1 v2; req emp; f(v1, v2); req emp; ens res=v1+1
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
       {|xs=1+1|} ["a"]
       {|a=1/\xs=a|});
  [%expect {| false |}]

let%expect_test "union find" =
  let a = U.make (TVar "a") in
  let b = U.make Int in
  let c = U.make (TVar "c") in
  Format.printf "a: %s@." (string_of_type (U.get a));
  Format.printf "b: %s@." (string_of_type (U.get b));
  Format.printf "c: %s@." (string_of_type (U.get c));
  U.merge min_typ a b;
  U.merge min_typ a c;
  Format.printf "a: %s@." (string_of_type (U.get a));
  Format.printf "b: %s@." (string_of_type (U.get b));
  Format.printf "c: %s@." (string_of_type (U.get c));
  [%expect
    {|
        a: 'a
        b: int
        c: 'c
        a: int
        b: int
        c: int
    |}]
