open Util.Strings

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
      Printf.eprintf
        "Parse error at line %d, column %d: unexpected token '%s'\n" line column
        token;
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
  | WAND -> "WAND"
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
    match tok with
    | EOF -> List.rev (tok :: tokens)
    | _ -> loop (tok :: tokens)
  in
  let tokens = loop [] in
  let s = tokens |> List.map show_token |> String.concat " " in
  Format.printf "%s@." s

let parse_term ?(ctx = SMap.empty) spec =
  Parser_state.init ctx;
  handle_error Parser.parse_term (Lexing.from_string spec)

let parse_staged_spec = parse_term
let parse_prop = parse_term
let parse_hprop = parse_term
let parse_decl decl = handle_error Parser.parse_decl (Lexing.from_string decl)

let test ?(dump = false) a =
  let check_round_tripping s =
    let s1 = Format.asprintf "%a@." Core.Pretty.pp_term (parse_term s) in
    if s <> s1 then Format.printf "round-tripping failed!@."
  in
  try
    let parsed = parse_term a in
    if dump then Format.printf "%a@." Core.Syntax.dump_term parsed;
    let s = Format.asprintf "%a@." Core.Pretty.pp_term parsed in
    Format.printf "%s@." s;
    check_round_tripping s
  with Failure s -> Format.printf "%s@." s

let%expect_test "basics" =
  test "true";
  [%expect {| true |}];

  debug_tokens "ens emp";
  test "ens emp";
  [%expect {|
    ENSURES EMP EOF
    ens emp
    |}];

  test "ens x=1";
  [%expect {| ens x=1 |}];

  test "ens emp; x. ens x=1";
  [%expect {| ens emp; x. ens x=1 |}];

  test "forall x y. ens x=y";
  [%expect {| forall x y. ens x=y |}];

  test "ex x y. ens x=y; r. ens x=y";
  [%expect {| ex x y. ens x=y; r. ens x=y |}];

  test "forall x. forall y. ens x=y";
  [%expect {| forall x. (forall y. ens x=y) |}]

let%expect_test "options" =
  test ~dump:true "None";
  [%expect {|
    None
    None
    |}];

  test ~dump:true "Some 1";
  [%expect {|
    Some (Int 1)
    Some 1
    |}];

  test ~dump:true "Some 1 + 1";
  [%expect {|
    Binop (Plus, Some (Int 1), Int 1)
    Some 1+1
    |}];

  (* TODO this is a problem *)
  test ~dump:true "k Some 1";
  [%expect {|
    Apply (Symbol k, [Symbol Some, Int 1])
    k Some 1
    |}]

let%expect_test "tuples" =
  (* empty tuples are not allowed *)
  test ~dump:true "()";
  [%expect {|
    Unit
    ()
    |}];

  (* single-element tuples are not allowed *)
  test ~dump:true "(1)";
  [%expect {|
    Int 1
    1
    |}];

  test ~dump:true "(1, 2)";
  [%expect {|
    Tuple [Int 1, Int 2]
    (1, 2)
    |}]

let%expect_test "application" =
  (* application of function to a single tuple value *)
  test "f(1,2)";
  [%expect {| f (1, 2) |}];

  (* application to multiple values *)
  test ~dump:true "f 1 2";
  [%expect {|
    Apply (Symbol f, [Int 1, Int 2])
    f 1 2
    |}];

  (* this gets normalised *)
  test ~dump:true "(f 1) 2";
  [%expect {|
    Apply (Symbol f, [Int 1, Int 2])
    f 1 2
    |}];

  (* TODO fix printing *)
  test ~dump:true "f (g 2)";
  [%expect {|
    Apply (Symbol f, [Apply (Symbol g, [Int 2])])
    f g 2
    |}];

  test ~dump:true "f (g 2) 3";
  [%expect {|
    Apply (Symbol f, [Apply (Symbol g, [Int 2]), Int 3])
    f g 2 3
    |}]

let%expect_test "definitions and entailments" =
  (* relative precedences for foldr *)
  test "ens xs=[]; init \\/ ex h t. ens xs=h::t; foldr f init t; r. f h r";
  [%expect
    {| ens xs=[]; init \/ (ex h t. ens xs=h::t; foldr f init t; r. f h r) |}];

  test "foldr (fun c t -> c+t) 0 [] <: sum []";
  [%expect {| foldr (fun c t -> c+t) 0 [] <: sum [] |}];

  test ~dump:true "ens (forall a. a=1); ens emp <: ens emp";
  [%expect
    {|
    Subsumes (Sequence (Ensures (Forall (a. Binop (Eq, Var a, Int 1))),
                Ensures (Emp)), Ensures (Emp))
    ens (forall a. a=1); ens emp <: ens emp
    |}];

  (* quantifiers *)
  test ~dump:true "forall a. ens a=1 <: ens emp";
  [%expect
    {|
    Forall (a. Subsumes (Ensures (Binop (Eq, Var a, Int 1)), Ensures (Emp)))
    forall a. ens a=1 <: ens emp
    |}];

  test ~dump:true "(ex a. ens a=1) <: ens emp";
  [%expect
    {|
    Subsumes (Exists (a. Ensures (Binop (Eq, Var a, Int 1))), Ensures (Emp))
    (ex a. ens a=1) <: ens emp
    |}]

let%expect_test "shadowing" =
  test "ens emp; x. ens emp; x. ens x=2";
  [%expect {| ens emp; x. ens emp; x1. ens x1=2 |}];

  test "ens emp; x. (ens x=1 \\/ (ens emp; x. ens x=2))";
  [%expect {| ens emp; x. (ens x=1 \/ ens emp; x1. ens x1=2) |}];

  test "ens emp; x. ((ens emp; x. ens x=2) \\/ ens x=1)";
  [%expect {| ens emp; x. (ens emp; x1. ens x1=2 \/ ens x=1) |}]

let%expect_test "precedence and associativity" =
  (* seq is right-associative *)
  test "ens emp; (ens emp; ens emp)";
  [%expect {| ens emp; ens emp; ens emp |}];

  test "(ens emp; ens emp); ens emp";
  [%expect {| (ens emp; ens emp); ens emp |}];

  test "ens emp; ens emp; ens emp";
  [%expect {| ens emp; ens emp; ens emp |}];

  (* seq has higher precedence than forall *)
  test "forall x. ens emp; ens emp";
  [%expect {| forall x. ens emp; ens emp |}];

  test "forall x. (ens emp; ens emp)";
  [%expect {| forall x. ens emp; ens emp |}];

  test "(forall x. ens emp); ens emp";
  [%expect {| (forall x. ens emp); ens emp |}];

  (* forall can technically appear on the right without parens,
    but our pretty printing is simple and does not take that into account *)
  test "ens emp; forall x. ens emp";
  [%expect {| ens emp; (forall x. ens emp) |}];

  (* ill-typed terms like these are possible *)
  test "ens (ens emp)";
  [%expect {| ens ens emp |}];

  (* seq has higher precedence than disj *)
  test "ens emp; ens emp \\/ ens emp";
  [%expect {| ens emp; ens emp \/ ens emp |}];

  test "(ens emp; ens emp) \\/ ens emp";
  [%expect {| ens emp; ens emp \/ ens emp |}];

  test "ens emp; (ens emp \\/ ens emp)";
  [%expect {| ens emp; (ens emp \/ ens emp) |}];

  (* disjunction is left-associative *)
  test "ens emp \\/ (ens emp \\/ ens emp)";
  [%expect {| ens emp \/ (ens emp \/ ens emp) |}];

  (* disj and quantifier precedence *)
  test "(forall x. ens x=1) \\/ ens emp";
  [%expect {| (forall x. ens x=1) \/ ens emp |}];

  test "forall x. (ens x=1 \\/ ens emp)";
  [%expect {| forall x. ens x=1 \/ ens emp |}];

  (* conj and relational operators *)
  test "ens x=1 /\\ y=2";
  [%expect {| ens x=1 /\ y=2 |}];

  test "ens x=1 /\\ ens y=2";
  [%expect {| ens x=1 /\ ens y=2 |}];

  (* wand and sep conj *)
  test "x->1 -* y->2";
  [%expect {| x->1 -* y->2 |}];

  test "(x->1 -* y->2) -* z->3";
  [%expect {| x->1 -* y->2 -* z->3 |}]

let%expect_test "shift/reset" =
  test "shift k 0";
  [%expect {| shift k 0 |}];

  test ~dump:true "shift k k 1";
  [%expect {|
    Shift (k. Apply (Var k, [Int 1]))
    shift k k 1
    |}];

  test "shift k k 1 + 2";
  [%expect {| shift k (k 1+2) |}]
