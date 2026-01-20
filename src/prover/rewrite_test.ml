open Rewrite
open Core.Pretty
open Parsing.Parse

let%expect_test _ =
  let test (rule : rule) term =
    let t0 = parse_term term in
    match rewrite rule t0 with
    | Some (t, side) ->
        Format.printf "%a ==> %a@." pp_term t0 pp_term t;
        (match side with
        | [] -> ()
        | _ :: _ -> Format.printf "%a@." (Fmt.list pp_term) side)
    | None -> Format.printf "rewrite failed@."
  in
  let rule : rule = prop_to_rule (parse_prop "true <: false") in
  test rule "true";
  [%expect {| true ==> false |}];

  let rule : rule = prop_to_rule (parse_prop "f (fun y -> y) <: g 1") in
  test rule "f (fun x -> x)";
  [%expect {| f (fun x -> x) ==> g 1 |}];

  let rule : rule = prop_to_rule (parse_prop "f (fun y z -> y z) <: g 1") in
  test rule "f (fun x a -> x a)";
  [%expect {| f (fun x a -> x a) ==> g 1 |}];

  let rule : rule = prop_to_rule (parse_prop "forall x. f 1 <: g 1") in
  test rule "f 1";
  [%expect {| rewrite failed |}]
