open Ocamlfrontend
open Core
open Pretty

let parse_spec s = Parser.only_effect_spec Lexer.token (Lexing.from_string s)

let parse_disj_spec s =
  Parser.only_disj_effect_spec Lexer.token (Lexing.from_string s)

let%expect_test "renaming existentials" =
  let show a = a |> string_of_disj_spec |> print_endline in
  Forward_rules.renamingexistientalVar (parse_disj_spec "ex a; Norm(a=1, a)")
  |> show;
  [%expect {|
|}]
