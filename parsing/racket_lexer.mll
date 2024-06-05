{
open Lexing
open Racket_parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

(* part 1 *)
let int =  '-'? ['0'-'9'] ['0'-'9']*

(* part 2 *)
let decimal_literal =
  ['0'-'9'] ['0'-'9' '_']*
let hex_digit =
  ['0'-'9' 'A'-'F' 'a'-'f']
let hex_literal =
  '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']*
let oct_literal =
  '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
let bin_literal =
  '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
let int_literal =
  decimal_literal | hex_literal | oct_literal | bin_literal

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?

(* part 3 *)
let white = [' ' '\t']+
let newline = '\n' | '\r' | "\r\n" 
let id = ['a'-'v' 'x'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*


let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule token =
  parse
  | white    { token lexbuf }
  | newline  { next_line lexbuf; token lexbuf }
  | "true"   { TRUE }
  | "false"  {FALSE}
  | "fun"  {FUN}
  | "shift" {SHIFT}
  | "reset" {RESET}
  | "lambda" {LAMBDA}
  | "require" {REQUIRE}
  | "lang" {LANG}
  | "define" {DEFINE}
  | "/" {SLASH}
  | '#' { SHARP }
  | '(' { LPAREN } 
  | ')' { RPAREN }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | ";"  { SEMI }
  | ","  { COMMA }
  | "+"  { PLUS }
  | "&&" { AMPERAMPER }
  | "->" { MINUSGREATER }
  | "(*@"
      { LSPECCOMMENT } 
  | "@*)"
      { RSPECCOMMENT }
  | "-"  { MINUS }
  | id as str { LIDENT str }
  | int_literal as lit { INT (lit) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }

