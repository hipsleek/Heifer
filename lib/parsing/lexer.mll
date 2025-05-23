{
(* open Lexing *)
open Parser

}

let blank = [' ']
let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']
let ident = (lowercase | uppercase) identchar*
let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
let int_literal = decimal_literal

rule token = parse
  | blank +
      { token lexbuf }
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
