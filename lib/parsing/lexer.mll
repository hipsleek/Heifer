{
(* open Lexing *)
open Parser

}

let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']
let ident = (lowercase | uppercase) identchar*
let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
let int_literal = decimal_literal

rule token = parse
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
  | "*"
      { STAR }
  | "."
      { DOT }
  | ";"
      { SEMICOLON }
