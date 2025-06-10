{
open Parser

exception Lexing_error of string

let raise_error lexbuf msg =
  let pos = Lexing.lexeme_start_p lexbuf in
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  raise (Lexing_error (Printf.sprintf "Line %d, character %d: %s" l c msg))

}

let blank = [' ' '\t']
let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']
let ident = (lowercase | uppercase) identchar*
let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
let int_literal = decimal_literal

rule token = parse
  | blank +
      { token lexbuf }
  | '\n' | '\r' | "\r\n"
    { Lexing.new_line lexbuf; token lexbuf }
  | "="
      { EQUAL }
  | ">"
      { GREATER }
  | "<"
      { LESS }
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
  | "ex"
      { EXISTS }
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
  | identchar + as v
      { IDENT v }
  | _ as c
    { raise_error lexbuf (Printf.sprintf "Unexpected character: '%c'" c) }
