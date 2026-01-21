open Shift_reset
open Core.Pretty
open Parsing.Parse

let test input =
  let input = parse_term input in
  let output = reduce input in
  Format.printf "%a" pp_term output

let%expect_test "reset without shift" =
  test "reset (1)";
  [%expect {| 1 |}];

  test "reset (2)";
  [%expect {| 2 |}];

  test "reset (reset (1))";
  [%expect {| 1 |}];

  test "reset (reset (true))";
  [%expect {| true |}];

  test "reset (reset (false))";
  [%expect {| false |}];

  test "reset (ens 1=1; req 1=1)";
  [%expect {| ens 1=1; req 1=1 |}];

  test {| forall f x. reset (ens 1=1; f x) |};
  [%expect {| forall f x. ens 1=1; reset (f x) |}];

  test {| forall f x. reset ((ens 1=1 \/ req 1=1); f x) |};
  [%expect {| forall f x. ens 1=1; reset (f x) \/ req 1=1; reset (f x) |}];

  test {| reset (1; r. ens r=1) |};
  [%expect {| ens 1=1 |}];

  test {| reset ((true; r. ens r=true); r. r) |};
  [%expect {| ens true=true; () |}];

  test {| forall x. reset ((ens x=1; r. ens x=r); r. req r=()) |};
  [%expect {| forall x. ens x=1; ens x=(); req ()=() |}]

let%expect_test "reset with shift" =
  ()
