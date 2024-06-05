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
  | "shift" {SHIFT}
  | "reset" {RESET}
  | "lambda" {LAMBDA}
  | "require" {REQUIRE}
  | "lang" {LANG}
  | "define" {DEFINE}
  | "/" {SLASH}
  | '#' { SHARP }
  | '(' { LPAR } 
  | ')' { RPAR }
  | '[' { LBrackets }
  | ']' { RBrackets }
  | id as str { LVAR str }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }

