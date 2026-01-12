let handle_error parser lexbuf =
  try parser Lexer.token lexbuf with
  | Lexer.Lexing_error msg ->
    Printf.eprintf "Lexing error: %s\n" msg;
    failwith "lexer error"
  | Parser.Error ->
    let pos = Lexing.lexeme_start_p lexbuf in
    let line = pos.Lexing.pos_lnum in
    let column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
    let token = Lexing.lexeme lexbuf in
    Printf.eprintf "Parse error at line %d, column %d: unexpected token '%s'\n"
      line column token;
    failwith "parse error"

let show_token (tok : Parser.token) =
  match tok with
  | SUBSUMES -> "SUBSUMES"
  | STAR -> "STAR"
  | TRUE -> "TRUE"
  | TILDE -> "TILDE"
  | STARDOT -> "STARDOT"
  | COLONCOLON -> "COLONCOLON"
  | SHIFT -> "SHIFT"
  | SEMI -> "SEMI"
  | RPAREN -> "RPAREN"
  | RESET -> "RESET"
  | RETURN -> "RETURN"
  | REQUIRES -> "REQUIRES"
  | RBRACKET -> "RBRACKET"
  | PLUS -> "PLUS"
  | DOLLAR -> "DOLLAR"
  | MINUSGREATER -> "MINUSGREATER"
  | EQUALGREATER -> "EQUALGREATER"
  | MINUS -> "MINUS"
  | LPAREN -> "LPAREN"
  | LONGARROW -> "LONGARROW"
  | LET -> "LET"
  | LESS -> "LESS"
  | LBRACKET -> "LBRACKET"
  | IN -> "IN"
  | GREATER -> "GREATER"
  | FUN -> "FUN"
  | FORALL -> "FORALL"
  | FALSE -> "FALSE"
  | EXISTS -> "EXISTS"
  | EQUAL -> "EQUAL"
  | EOF -> "EOF"
  | ENSURES -> "ENSURES"
  | EMP -> "EMP"
  | DOT -> "DOT"
  | DISJUNCTION -> "DISJUNCTION"
  | CONJUNCTION -> "CONJUNCTION"
  | COMMA -> "COMMA"
  | STRING s -> Format.asprintf "STRING %s" s
  | LOWERCASE_IDENT s -> Format.asprintf "LOWERCASE_IDENT %s" s
  | INT i -> Format.asprintf "INT %d" i
  | CAPITAL_IDENT s -> Format.asprintf "CAPITAL_IDENT %s" s

let debug_tokens str =
  let lb = Lexing.from_string str in
  let rec loop tokens =
    let tok = Lexer.token lb in
    match tok with EOF -> List.rev (tok :: tokens) | _ -> loop (tok :: tokens)
  in
  let tokens = loop [] in
  let s = tokens |> List.map show_token |> String.concat " " in
  Format.printf "%s@." s
(* debug ~at:3 ~title:"debug tokens" "%s" s *)

let parse_term spec = handle_error Parser.parse_term (Lexing.from_string spec)
let parse_staged_spec = parse_term
let parse_prop = parse_term
let parse_hprop = parse_term
let parse_decl decl = handle_error Parser.parse_decl (Lexing.from_string decl)

open Core.Pretty

let term a = Format.printf "%a@." pp_term (parse_term a)

let%expect_test "basics" =
  (* TODO test round-tripping *)
  term "true";
  [%expect {| true |}];

  debug_tokens "ens emp";
  term "ens emp";
  [%expect {|
    ENSURES EMP EOF
    ens emp
    |}];

  term "ens x=1";
  [%expect {| ens x=1 |}];
  term "ens emp; x. ens x=1";
  [%expect {| ens emp; x. ens x=1 |}];

  term "forall x y. ens x=y";
  [%expect {| forall x y. ens x=y |}];
  term "ex x y. ens x=y";
  [%expect {| ex x y. ens x=y |}]
(* ;

  term "ex x y. ens x=y; r. ens x=y";
  [%expect {| ex x y. ens x=y; r. ens x=y |}] *)
(* ;

  (* application of function to a single tuple value *)
  term "f(1,2)";
  [%expect {| f (1, 2) |}];

  (* application to multiple values *)
  term "f 1 2";
  [%expect {| f 1 2 |}];

  (* relative precedences for foldr *)
  term "ens xs=[]; ret init \\/ ex h t. ens xs=h::t; foldr f init t; r. f h r";
  [%expect
    {| ens xs=[]; ret init \/ ex h t. ens xs=h::t; foldr f init t; r. f h r |}];

  term "foldr (fun c t -> ret c+t) 0 []";
  [%expect {| foldr (fun c t -> ret c+t) 0 [] |}];
  term "ret sum$([])";
  [%expect {| ret sum$([]) |}] *)

(* let%expect_test "shadowing" =
  term "ens emp; x. ens emp; x. ens x=2";
  [%expect {| ens emp; x. ens emp; x1. ens x1=2 |}];

  term "ens emp; x. (ens x=1 \\/ (ens emp; x. ens x=2))";
  [%expect {| ens emp; x. (ens x=1 \/ ens emp; x1. ens x1=2) |}];

  term "ens emp; x. ((ens emp; x. ens x=2) \\/ ens x=1)";
  [%expect {| ens emp; x. (ens emp; x1. ens x1=2 \/ ens x=1) |}]

let%expect_test "precedence and associativity" =
  (* seq is right-associative *)
  term "ens emp; (ens emp; ens emp)";
  [%expect {| ens emp; ens emp; ens emp |}];

  term "(ens emp; ens emp); ens emp";
  [%expect {| (ens emp; ens emp); ens emp |}];

  term "ens emp; ens emp; ens emp";
  [%expect {| ens emp; ens emp; ens emp |}];

  (* seq has higher precedence than disj *)
  term "ens emp; ens emp \\/ ens emp";
  [%expect {| ens emp; ens emp \/ ens emp |}];

  term "(ens emp; ens emp) \\/ ens emp";
  [%expect {| ens emp; ens emp \/ ens emp |}];

  term "ens emp; (ens emp \\/ ens emp)";
  [%expect {| ens emp; (ens emp \/ ens emp) |}];

  (* disj and quantifier precedence *)
  term "(forall x. ens x=1) \\/ ens emp";
  [%expect {| forall x. ens x=1 \/ ens emp |}];

  term "forall x. (ens x=1 \\/ ens emp)";
  [%expect {| forall x. (ens x=1 \/ ens emp) |}] *)
