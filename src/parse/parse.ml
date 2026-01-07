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
  | STAR -> "STAR"
  | TRUE -> "TRUE"
  | TILDE -> "TILDE"
  | STARDOT -> "STARDOT"
  | COLONCOLON -> "COLONCOLON"
  | SHIFT -> "SHIFT"
  | SEMI -> "SEMI"
  | RPAREN -> "RPAREN"
  | RESET -> "RESET"
  | REQUIRES -> "REQUIRES"
  | RBRACKET -> "RBRACKET"
  | PLUS -> "PLUS"
  | MINUSGREATER -> "MINUSGREATER"
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

let parse_prop spec = handle_error Parser.parse_prop (Lexing.from_string spec)

let parse_staged_spec spec =
  handle_error Parser.parse_staged_spec (Lexing.from_string spec)

(* open Parsing *)

(*


let parse_lemma spec =
  handle_error Parser.parse_lemma (Lexing.from_string spec)

let parse_kappa spec = Parser.parse_kappa Lexer.token (Lexing.from_string spec)

let parse_term spec = Parser.parse_term Lexer.token (Lexing.from_string spec)

let parse_state spec = Parser.parse_state Lexer.token (Lexing.from_string spec)

let string_of_payload (p : Parsetree.payload) =
  match p with
  | PStr [{
      pstr_desc = Pstr_eval ({
        pexp_desc = Pexp_constant {
          pconst_desc = Pconst_string (annotation, _, _); _}; _}, _); _}] ->
            Some annotation
  | _ -> None

let attribute_parser (attr_name : string) (payload_parser : Parsetree.payload -> 'a option) attr =
  let open Ocaml_compiler.Ocaml_common.Parsetree in
  (* TODO use ppxlib to do this matching instead; it would be a lot cleaner... *)
  if String.equal attr.attr_name.txt attr_name
  then payload_parser attr.attr_payload
  else None

let parse_spec_attribute = attribute_parser "spec" (fun p -> Option.map parse_staged_spec (string_of_payload p))
let parse_ignore_attribute = attribute_parser "ignore" (fun _ -> Some ())
let parse_lemma_attribute = attribute_parser "lemma" (fun p -> Option.map parse_lemma (string_of_payload p))

let extract_attribute parser attrs =
  match List.filter_map parser attrs with
  | item :: _ -> Some item
  | _ -> None

let extract_spec_attribute attrs = extract_attribute parse_spec_attribute attrs
let extract_ignore_attribute attrs = extract_attribute parse_ignore_attribute attrs *)

open Core.Pretty

let term a = Format.printf "%a@." pp_prop (parse_prop a)
let staged a = Format.printf "%a@." pp_staged_spec (parse_staged_spec a)

let%expect_test "basics" =
  (* TODO test round-tripping *)
  term "true";
  [%expect {| true |}];

  debug_tokens "ens emp";
  staged "ens emp";
  [%expect {|
    ENSURES EMP EOF
    ens emp
    |}];

  staged "ens x=1";
  [%expect {| ens x=1 |}];

  staged "ens emp; x. ens x=1";
  [%expect {| ens emp; x. ens x=1 |}];

  staged "forall x y. ens x=y";
  [%expect {| forall x y. ens x=y |}];

  staged "ex x y. ens x=y";
  [%expect {| ex x y. ens x=y |}];

  debug_tokens "f(1,2)";
  staged "f(1,2)";
  [%expect
    {|
    LOWERCASE_IDENT f LPAREN INT 1 COMMA INT 2 RPAREN EOF
    f(1, 2)
    |}];

  staged
    "ens xs=[]; ret init \\/ ex h t. ens xs=h::t; foldr(f, init, t); r. f(h, r)";
  [%expect
    {| ens xs=[]; retinit \/ ex h1 t. ens xs=h1::t; foldr(f, init, t); r. f(h, r) |}]

let%expect_test "shadowing" =
  staged "ens emp; x. ens emp; x. ens x=2";
  [%expect {| ens emp; x. ens emp; x1. ens x1=2 |}];

  staged "ens emp; x. (ens x=1 \\/ (ens emp; x. ens x=2))";
  [%expect {| ens emp; x. (ens x=1 \/ ens emp; x1. ens x1=2) |}];

  staged "ens emp; x. ((ens emp; x. ens x=2) \\/ ens x=1)";
  [%expect {| ens emp; x. (ens emp; x1. ens x1=2 \/ ens x=1) |}]

let%expect_test "precedence and associativity" =
  (* seq is right-associative *)
  staged "ens emp; (ens emp; ens emp)";
  [%expect {| ens emp; ens emp; ens emp |}];

  staged "(ens emp; ens emp); ens emp";
  [%expect {| (ens emp; ens emp); ens emp |}];

  staged "ens emp; ens emp; ens emp";
  [%expect {| ens emp; ens emp; ens emp |}];

  (* seq has higher precedence than disj *)
  staged "ens emp; ens emp \\/ ens emp";
  [%expect {| ens emp; ens emp \/ ens emp |}];

  staged "(ens emp; ens emp) \\/ ens emp";
  [%expect {| ens emp; ens emp \/ ens emp |}];

  staged "ens emp; (ens emp \\/ ens emp)";
  [%expect {| ens emp; (ens emp \/ ens emp) |}]
