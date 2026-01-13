open Prenex
open Core.Pretty
open Parsing.Parse

let%expect_test "prenex" =
  let test s =
    let f = parse_staged_spec s in
    let f = prenex f in
    Format.printf "%a@." pp_term f
  in
  test "ens emp; r. ex a. ens a=1";
  [%expect {| ens emp; r. (ex a. ens a=1) |}];

  test "ens emp; r. (forall a. ens a=1 \\/ ens emp)";
  [%expect {| ens emp; r. (forall a. ens a=1 \/ ens emp) |}];

  (* quantifiers don't get lifted out of a reset *)
  test "reset (forall a. ens a=1)";
  [%expect {| reset (forall a. ens a=1) |}];

  test "ens emp; r. ens (forall a. a=1)";
  [%expect {| ens emp; r. ens forall a. a=1 |}];

  test "(forall x. ens x=1); ens 1=1";
  [%expect {| forall x. ens x=1; ens 1=1 |}];

  test "((forall x. ens x=1); ens 1=1); ens 2=2";
  [%expect {| forall x. (ens x=1; ens 1=1); ens 2=2 |}];

  test "(exists x. ens x=1); ens 1=1";
  [%expect {| ex x. ens x=1; ens 1=1 |}];

  test "((exists x. ens x=1); ens 1=1); ens 2=2";
  [%expect {| ex x. (ens x=1; ens 1=1); ens 2=2 |}];

  test "forall x. (exists y. req x=y); ens 1=1";
  [%expect {| forall x. (ex y. req x=y; ens 1=1) |}]
