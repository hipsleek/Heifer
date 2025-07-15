{
open Parser

exception Lexing_error of string

let raise_error lexbuf msg =
  let pos = Lexing.lexeme_start_p lexbuf in
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  raise (Lexing_error (Printf.sprintf "Line %d, character %d: %s" l c msg))

let string_buffer = Buffer.create 256
let reset_string_buffer () = Buffer.reset string_buffer
let get_stored_string () = Buffer.contents string_buffer

let store_string_char c = Buffer.add_char string_buffer c
let store_string s = Buffer.add_string string_buffer s
let store_substring s ~pos ~len = Buffer.add_substring string_buffer s pos len

let store_lexeme lexbuf = store_string (Lexing.lexeme lexbuf)

let wrap_string_lexer lexer lexbuf =
  reset_string_buffer ();
  lexer lexbuf;
  get_stored_string ()

let store_normalized_newline nl =
  let len = String.length nl in
  if len = 1
  then store_string_char '\n'
  else store_substring nl ~pos:1 ~len:(len - 1)
}

let newline = '\r'* '\n'
let blank = [' ' '\t']
let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']
let ident = (lowercase | uppercase) identchar*
let lowercase_ident = lowercase identchar*
let uppercase_ident = uppercase identchar*
let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
let int_literal = decimal_literal

rule token = parse
  | blank +
      { token lexbuf }
  | newline
      { Lexing.new_line lexbuf; token lexbuf }
  | "="
      { EQUAL }
  | ">"
      { GREATER }
  | "==>"
      { LONGARROW }
  | "<"
      { LESS }
  | "*."
      { STARDOT }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | "*"
      { STAR }
  | "->"
      { MINUSGREATER }
  | "."
      { DOT }
  | "~"
      { TILDE }
  | "/\\"
      { CONJUNCTION }
  | "\\/"
      { DISJUNCTION }
  | "("
      { LPAREN }
  | ")"
      { RPAREN }
  | "["
      { LBRACKET }
  | "]"
      { RBRACKET }
  | ";"
      { SEMI }
  | ","
      { COMMA }
  | "true"
      { TRUE }
  | "false"
      { FALSE }
  | "emp"
      { EMP }
  | int_literal as n
      { INT (int_of_string n) }
  | "ex" | "exists"
      { EXISTS }
  | "all" | "forall"
      { FORALL }
  | "req"
      { REQUIRES }
  | "ens"
      { ENSURES }
  | "let"
      { LET }
  | "in"
      { IN }
  | "sh"
      { SHIFT }
  | "rs"
      { RESET }
  | eof
      { EOF }
  | '"'
      { let s = wrap_string_lexer string lexbuf in
        STRING (s) }
  | uppercase_ident as v
      { CAPITAL_IDENT v}
  | lowercase_ident as v
      { LOWERCASE_IDENT v }
  | _ as c
      { raise_error lexbuf (Printf.sprintf "Unexpected character: '%c'" c) }

and string = parse
  | '"'
      { () }
  | newline as nl
      { Lexing.new_line lexbuf;
        store_normalized_newline nl;
        string lexbuf }
  | eof
      { raise_error lexbuf "Unterminated string" }
  | (_ as c)
      { store_string_char c; string lexbuf }
