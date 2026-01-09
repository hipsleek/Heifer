open Tactic.ProofState
open Tactic.Interactive

let%expect_test "reflexivity" =
  start_proof "ens emp" "ens emp";
  refl ();
  [%expect
    {|
    ----------------------------------------
      ens emp
    ⊑ ens emp

    no more goals
    |}]

let%expect_test "specialize" =
  start_proof "ens forall a. a=1; ens emp" "ens emp";
  intro_pure "H";
  specialize "H" ["1"];
  [%expect
    {|
    ----------------------------------------
      ens forall a. a=1; ens emp⊑ ens emp

    H: forall a. a=1
    ----------------------------------------
      ens emp
    ⊑ ens emp


    H: 1=1
    ----------------------------------------
      ens emp
    ⊑ ens emp
    |}]

let%expect_test "intro heap" =
  start_proof "ens x->1; ens emp" "ens emp";
  intro_heap ();
  [%expect
    {|
    ----------------------------------------
      ens x->1; ens emp
    ⊑ ens emp


    ----------------------------------------
    x->1
    ---------------------------------------*
      ens emp
    ⊑ ens emp
    |}]

let%expect_test "forall intro" =
  start_proof "ens emp" "forall a. ens a=1";
  forall_intro ();
  [%expect
    {|
    ----------------------------------------
      ens emp
    ⊑ forall a. ens a=1

    a
    ----------------------------------------
      ens emp
    ⊑ ens a=1
    |}]

let%expect_test "forall elim" =
  start_proof "forall a. ens a=1" "ens emp";
  forall_elim ["1"];
  [%expect
    {|
    ----------------------------------------
      forall a. ens a=1
    ⊑ ens emp


    ----------------------------------------
      ens 1=1
    ⊑ ens emp
    |}]

let%expect_test "exists elim" =
  start_proof "exists a. ens a=1" "ens emp";
  exists_elim ();
  [%expect
    {|
    ----------------------------------------
      ex a. ens a=1
    ⊑ ens emp

    a
    ----------------------------------------
      ens a=1
    ⊑ ens emp
    |}]

let%expect_test "exists intro" =
  start_proof "ens emp" "exists a. ens a=1";
  exists_intro ["1"];
  [%expect
    {|
    ----------------------------------------
      ens emp
    ⊑ ex a. ens a=1


    ----------------------------------------
      ens emp
    ⊑ ens 1=1
    |}]

let%expect_test "disj_elim" =
  start_proof "ens emp \\/ ens emp" "ens emp";
  disj_elim ();
  [%expect
    {|
    ----------------------------------------
      ens emp \/ ens emp
    ⊑ ens emp


    ----------------------------------------
      ens emp
    ⊑ ens emp
    (1 more goals)
    |}]

let%expect_test "left/right" =
  start_proof "ens emp" "(ens 1=1 \\/ ens 2=2) \\/ ens 3=3";
  left ();
  right ();
  [%expect
    {|
    ----------------------------------------
      ens emp
    ⊑ ens 1=1 \/ ens 2=2 \/ ens 3=3


    ----------------------------------------
      ens emp
    ⊑ ens 1=1 \/ ens 2=2


    ----------------------------------------
      ens emp
    ⊑ ens 2=2
    |}]

let%expect_test "simpl" =
  start_proof "ens emp; r. ens emp" "ens emp";
  simpl ();
  [%expect
    {|
    ----------------------------------------
      ens emp; r. ens emp
    ⊑ ens emp


    ----------------------------------------
      ens emp; ens emp; ret ()
    ⊑ ens emp
    |}];

  start_proof "ret 1; r. ens r=1" "ens emp";
  simpl ();
  [%expect
    {|
    ----------------------------------------
      ret 1; r. ens r=1
    ⊑ ens emp


    ----------------------------------------
      ens 1=1; ret ()
    ⊑ ens emp
    |}]

let%expect_test "declare functions" =
  reset_proof_state ();
  declare "succ x = ret x + 1";
  [%expect
    {| succ declared |}
  ]
