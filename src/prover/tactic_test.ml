open Tactic.ProofState
open Tactic.Interactive

let%expect_test "reflexivity" =
  start_proof "ens emp <: ens emp";
  refl ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    no more goals
    |}];

  start_proof "ens emp <: ens x=1";
  refl ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens x=1


    error: cannot close goal using reflexivity
    |}]

let%expect_test "specialize" =
  start_proof "ens (forall a. a=1); ens emp <: ens emp";
  intro_pure "H";
  specialize "H" ["1"];
  [%expect
    {|
    ----------------------------------------
       ens (forall a. a=1); ens emp
    <: ens emp



    H: forall a. a=1
    ----------------------------------------
       ens emp
    <: ens emp



    H: 1=1
    ----------------------------------------
       ens emp
    <: ens emp
    |}];

  start_proof "ens a=1; ens emp <: ens emp";
  intro_pure "H";
  specialize "H" ["1"];
  [%expect
    {|
    ----------------------------------------
       ens a=1; ens emp
    <: ens emp



    H: a=1
    ----------------------------------------
       ens emp
    <: ens emp


    error: not a prop that can be specialised
    |}];

  start_proof "ens emp <: ens emp";
  specialize "H" ["1"];
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: no assumption named: H
    |}]

let%expect_test "intro heap" =
  start_proof "ens x->1; ens emp <: ens emp";
  intro_heap ();
  [%expect
    {|
    ----------------------------------------
       ens x->1; ens emp
    <: ens emp



    ----------------------------------------
    x->1
    ---------------------------------------*
       ens emp
    <: ens emp
    |}];

  start_proof "ens x->1 <: ens emp";
  intro_heap ();
  [%expect
    {|
    ----------------------------------------
       ens x->1
    <: ens emp



    ----------------------------------------
    x->1
    ---------------------------------------*
       ens emp
    <: ens emp
    |}];

  start_proof "1 <: ens emp";
  intro_heap ();
  [%expect
    {|
    ----------------------------------------
       1
    <: ens emp


    error: failed to intro heap / cannot uncons req / cannot uncons ens
    |}]

let%expect_test "forall intro" =
  start_proof "ens emp <: forall a. ens a=1";
  forall_intro ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: forall a. ens a=1


    a
    ----------------------------------------
       ens emp
    <: ens a=1
    |}];

  start_proof "ens emp <: ens emp";
  forall_intro ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: empty choice / not a forall / not a forall
    |}]

let%expect_test "forall elim" =
  start_proof "(forall a. ens a=1) <: ens emp";
  forall_elim ["1"];
  [%expect
    {|
    ----------------------------------------
       forall a. ens a=1
    <: ens emp



    ----------------------------------------
       ens 1=1
    <: ens emp
    |}];

  start_proof "ens emp <: ens emp";
  forall_elim ["1"];
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: cannot eliminate forall
    |}]

let%expect_test "exists elim" =
  start_proof "(exists a. ens a=1) <: ens emp";
  exists_elim ();
  [%expect
    {|
    ----------------------------------------
       ex a. ens a=1
    <: ens emp


    a
    ----------------------------------------
       ens a=1
    <: ens emp
    |}];

  start_proof "ens emp <: ens emp";
  exists_elim ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: cannot eliminate exists
    |}]

let%expect_test "exists intro" =
  start_proof "ens emp <: exists a. ens a=1";
  exists_intro ["1"];
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ex a. ens a=1



    ----------------------------------------
       ens emp
    <: ens 1=1
    |}];

  start_proof "ens emp <: ens emp";
  exists_intro ["1"];
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: cannot intro exists
    |}]

let%expect_test "disj_elim" =
  start_proof "ens emp \\/ ens emp <: ens emp";
  disj_elim ();
  [%expect
    {|
    ----------------------------------------
       ens emp \/ ens emp
    <: ens emp



    ----------------------------------------
       ens emp
    <: ens emp
    (1 more goals)
    |}];

  start_proof "ens emp <: ens emp";
  disj_elim ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: not a disjunction
    |}]

let%expect_test "left/right" =
  start_proof "ens emp <: (ens 1=1 \\/ ens 2=2) \\/ ens 3=3";
  left ();
  right ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens 1=1 \/ ens 2=2 \/ ens 3=3



    ----------------------------------------
       ens emp
    <: ens 1=1 \/ ens 2=2



    ----------------------------------------
       ens emp
    <: ens 2=2
    |}];

  start_proof "ens emp <: ens emp";
  left ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: not a disjunction
    |}];

  start_proof "ens emp <: ens emp";
  right ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: not a disjunction
    |}]

let%expect_test "simpl" =
  start_proof "ens emp; r. ens emp <: ens emp";
  simpl ();
  [%expect
    {|
    ----------------------------------------
       ens emp; r. ens emp
    <: ens emp



    ----------------------------------------
       ens emp; r. ens emp
    <: ens emp
    |}];

  start_proof "1; r. ens r=1 <: ens emp";
  simpl ();
  [%expect
    {|
    ----------------------------------------
       1; r. ens r=1
    <: ens emp



    ----------------------------------------
       ens 1=1
    <: ens emp
    |}]

let%expect_test "induction" =
  (* there are two variables named n, and we are doing induction on the existentially-quantified one *)
  start_proof "(ex n. ens n > 0; ens emp) <: forall n. req n > 0; ens n = 1";
  exists_elim ();
  intro_pure "Hn";
  forall_intro ();
  induction (`Int 0) "n" ~name:"IH";
  [%expect
    {|
    ----------------------------------------
       ex n. ens n>0; ens emp
    <: forall n. req n>0; ens n=1


    n
    ----------------------------------------
       ens n>0; ens emp
    <: forall n. req n>0; ens n=1


    n
    Hn: n>0
    ----------------------------------------
       ens emp
    <: forall n. req n>0; ens n=1


    n, n1
    Hn: n>0
    ----------------------------------------
       ens emp
    <: req n1>0; ens n1=1


    n, n1
    Hn: n>0
    IH: forall n2. ge n2 0 /\ lt n2 n => ens emp <: req n1>0; ens n1=1
    ----------------------------------------
       ens emp
    <: req n1>0; ens n1=1
    |}];

  start_proof "ens emp <: forall xs. length xs > 0";
  forall_intro ();
  induction `List "xs" ~name:"IH";
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: forall xs. length xs>0


    xs
    ----------------------------------------
       ens emp
    <: length xs>0


    xs
    IH: forall xs1. sublist xs1 xs => ens emp <: length xs1>0
    ----------------------------------------
       ens emp
    <: length xs>0
    |}];

  start_proof "ens emp <: ens emp";
  induction `List "n" ~name:"IH";
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: no constant named: n
    |}]

let%expect_test "unfold" =
  reset_proof_state ();
  declare "succ x = x + 1";
  start_proof "ens emp <: succ 1; r. ens 2 = r";
  unfold "succ";
  [%expect
    {|
    succ declared

    ----------------------------------------
       ens emp
    <: succ 1; r. ens 2=r



    ----------------------------------------
       ens emp
    <: 1+1; r. ens 2=r
    |}];

  start_proof "ens emp <: ens emp";
  unfold "foo";
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: the symbol foo does not exist
    |}]

let%expect_test "intro_pure" =
  start_proof "ens x=1 <: ens emp";
  intro_pure "H";
  [%expect
    {|
    ----------------------------------------
       ens x=1
    <: ens emp



    H: x=1
    ----------------------------------------
       ens emp
    <: ens emp
    |}];

  start_proof "ens x->1 <: ens emp";
  intro_pure "H";
  [%expect
    {|
    ----------------------------------------
       ens x->1
    <: ens emp


    error: failed to intro pure / cannot uncons pure req / cannot uncons pure ens
    |}];

  start_proof "ens a=1 <: ens emp";
  intro_pure "H";
  [%expect
    {|
    ----------------------------------------
       ens a=1
    <: ens emp



    H: a=1
    ----------------------------------------
       ens emp
    <: ens emp
    |}];

  start_proof "ens a=1; ens b=2; ens emp <: ens emp";
  intro_pure "H";
  intro_pure "H";
  [%expect
    {|
    ----------------------------------------
       ens a=1; ens b=2; ens emp
    <: ens emp



    H: a=1
    ----------------------------------------
       ens b=2; ens emp
    <: ens emp


    error: failed to intro pure / cannot uncons pure req / add_assumption: H is already used
    |}]

let%expect_test "rewrite" =
  start_proof "ens a=1; ens a=2 <: ens emp";
  (* TODO should this work? *)
  (* intro_pure "H"; *)
  (* rewrite "H"; *)
  [%expect
    {|
    ----------------------------------------
       ens a=1; ens a=2
    <: ens emp
    |}];

  start_proof "ens emp <: ens emp";
  rewrite "H";
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: ens emp


    error: no assumption named: H
    |}]

let%expect_test "heap tactics" =
  start_proof "ens emp <: forall x. req x->1; ens x->1";
  forall_intro ();
  req_left ();
  cancel_heap ();
  refl ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: forall x. req x->1; ens x->1


    x
    ----------------------------------------
       ens emp
    <: req x->1; ens x->1


    x
    ----------------------------------------
       ens x->1; ens emp
    <: ens x->1


    x
    ----------------------------------------
       ens emp; ens emp
    <: ens emp; ens emp


    no more goals
    |}];

  start_proof "ens emp <: forall x. req x->1; ens x->1";
  forall_intro ();
  intro_heap ();
  cancel_heap ();
  [%expect
    {|
    ----------------------------------------
       ens emp
    <: forall x. req x->1; ens x->1


    x
    ----------------------------------------
       ens emp
    <: req x->1; ens x->1


    x
    ----------------------------------------
    x->1
    ---------------------------------------*
       ens emp
    <: ens x->1


    x
    ----------------------------------------
       ens emp
    <: ens emp; ens emp
    |}]
