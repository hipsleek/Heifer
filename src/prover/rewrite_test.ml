open Rewrite
open Core.Pretty
open Parsing.Parse

let%expect_test _ =
  let test ?(direction = `Ltr) rule term =
    let rule = make_rule ~direction (parse_prop rule) in
    let target = parse_term term in
    try
      let result, conditions = rewrite rule target in
      Format.printf "%a ==> %a@." pp_term target pp_term result;
      if not (List.is_empty conditions) then Format.printf "%a@." (Fmt.list pp_term) conditions
    with Rewrite_failure msg -> Format.printf "error: %s@." msg
  in
  test "true <: false" "true";
  [%expect {| true ==> false |}];

  test "f (fun y -> y) <: g 1" "f (fun x -> x)";
  [%expect {| f (fun x -> x) ==> g 1 |}];

  test "f (fun y z -> y z) <: g 1" "f (fun x a -> x a)";
  [%expect {| f (fun x a -> x a) ==> g 1 |}];

  test "forall x. f 1 <: g 1" "f 1";
  [%expect {| error: no progress |}];

  test "forall x. x > 0 => f x = 0" "ens x > 0; r. f r";
  [%expect {| error: no progress |}]
