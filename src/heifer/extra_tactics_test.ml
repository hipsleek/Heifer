open Prover.Interactive.State
open Prover.Interactive
open Extra_tactics

let%expect_test "read_file" =
  let filename = "test_obs.ml" in
  let oc = open_out filename in
  output_string oc {|
let f x
(*@ 1 @*)
= 1

let g x
(*@ 1 @*)
= f x
|};
  close_out oc;
  reset_proof_state ();
  read_file filename;
  forall_intro ();
  refl ();
  Sys.remove filename;
  [%expect
    {|
    f declared
    g declared

    ────────────────────────────────────────────────────────────
    forall x. 1 <: 1
    (1 more goals)


    x
    ────────────────────────────────────────────────────────────
       1
    <: 1
    (1 more goals)


    H0: forall x. f x <: 1
    ────────────────────────────────────────────────────────────
    forall x. f x <: 1
    |}]
