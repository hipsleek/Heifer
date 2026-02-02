open Prenex
open Core.Pretty
open Parsing.Parse

let%expect_test "prenex_head" =
  let test term =
    let term = parse_term term in
    let term = prenex_head term in
    Format.printf "%a@." pp_term term
  in
  test "ens emp; r. ex a. ens a=1";
  [%expect {| ens emp; r. (ex a. ens a=1) |}];

  test "ens emp; r. (forall a. ens a=1 \\/ ens emp)";
  [%expect {| ens emp; r. (forall a. ens a=1 \/ ens emp) |}];

  (* quantifiers don't get lifted out of a reset *)
  test "reset (forall a. ens a=1)";
  [%expect {| reset (forall a. ens a=1) |}];

  test "ens emp; r. ens (forall a. a=1)";
  [%expect {| ens emp; r. ens (forall a. a=1) |}];

  test "(forall x. ens x=1); ens 1=1";
  [%expect {| forall x. ens x=1; ens 1=1 |}];

  test "((forall x. ens x=1); ens 1=1); ens 2=2";
  [%expect {| forall x. (ens x=1; ens 1=1); ens 2=2 |}];

  test "(exists x. ens x=1); ens 1=1";
  [%expect {| ex x. ens x=1; ens 1=1 |}];

  test "((exists x. ens x=1); ens 1=1); ens 2=2";
  [%expect {| ex x. (ens x=1; ens 1=1); ens 2=2 |}];

  test "forall x. (exists y. req x=y); ens 1=1";
  [%expect {| forall x. (ex y. req x=y; ens 1=1) |}];

  test "(forall x. ens x=1); ((forall y. ens y=2; ens y>0); ens emp)";
  [%expect {| forall x. ens x=1; (forall y. ens y=2; ens y>0); ens emp |}]

let%expect_test "prenex_assoc" =
  let test term =
    let term = parse_term term in
    let term = prenex_assoc term in
    Format.printf "%a@." pp_term term
  in
  (* quantifiers don't get lifted out of a reset *)
  test "reset (forall a. ens a=1)";
  [%expect {| reset (forall a. ens a=1) |}];

  test "ens emp; r. ens (forall a. a=1)";
  [%expect {| ens emp; r. ens (forall a. a=1) |}];

  test "((forall x. ens x=1); ens 1=1); ens 2=2";
  [%expect {| forall x. ens x=1; ens 1=1; ens 2=2 |}];

  test "((exists x. ens x=1); ens 1=1); ens 2=2";
  [%expect {| ex x. ens x=1; ens 1=1; ens 2=2 |}];

  test "forall x. (exists y. req x=y); ens 1=1";
  [%expect {| forall x. (ex y. req x=y; ens 1=1) |}];

  test "(forall x. ens x=1); ((forall y. ens y=2; ens y>0); ens emp)";
  [%expect {| forall x. ens x=1; (forall y. ens y=2; ens y>0; ens emp) |}];

  test {| forall a r. ens (a /\ r)=true; 1 \/ ens (a /\ r)=false |};
  [%expect {| forall a r. ens (a /\ r)=true; 1 \/ ens (a /\ r)=false |}]
