{
open Lexing
open Parser

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
let float = digit+ frac? exp?

(* part 3 *)
let white = [' ' '\t']+
let newline = '\n' | '\r' | "\r\n" 
let id = ['A'-'Z' 'a'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let op = ['+' '\\' '-' '/' '*' '=' '.' '$' '<' '>' ':' '&''|''^''?''%''#''@''~''!''+''|']+


rule token = parse
| white    { token lexbuf }
| newline  {(next_line lexbuf; token lexbuf) }
| int      { INTE (int_of_string (Lexing.lexeme lexbuf)) }


| eof { EOF }

| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }



| eof { EOF }

| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }


and read_single_line_comment = parse
  | newline { next_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { read_single_line_comment lexbuf }
  
and read_multi_line_comment = parse
  | "*)" { token lexbuf }
  | newline { next_line lexbuf; read_multi_line_comment lexbuf }
  | eof { raise (SyntaxError ("Lexer - Unexpected EOF - please terminate your comment.")) }
  | _ { read_multi_line_comment lexbuf }


(* part 5   *)

and read_string buf = parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }



(*

| ">=" {GTEQ}
| "<=" {LTEQ}
| '>' {GT}
| '<' {LT}
| '=' {EQ}
| ">=" {GTEQ}
| "<=" {LTEQ}
| "var" {VARKEY}
| "new" {NEW}
| "hiphop" {HIPHOP} 
| "module" {MODULE}
| "in" {IN}
| "out" {OUT}
| "emit" {EMIT}
| "await" {AWAIT}
| "do" {DO}
| "every" {EVERY}
| "fork" {FORK}
| "par" {PAR}
| "loop" {LOOP}
| "abort" {ABORT}
| "yield" {YIELD}
| "signal" {SIGNAL}
| "if" {IF}
| "halt" {HALT}
| "const" {CONST}
| "let" {LET}
| "hop" {HOP}
| "async" {ASYNC}
| "function" {FUNCTION}
| "return" {RETURN}
| "break" {BREAK}
| "else" {ELSE}
| "try" {TRY}
| "catch" {CATCH}
| "run" {RUN}
| "/*@" {LSPEC} 
| "@*/" {RSPEC}
| "=>" {IMPLY}
| "requires" {REQUIRE}
| "ensures" {ENSURE}
| '(' { LPAR }

| ')' { RPAR }
| '{' { LBRACK  }
| '}' { RBRACK }
| '.' { CONCAT }
| ':' { COLON }
| id as str { VAR str }
| '+' { PLUS }
| '-' { MINUS }
| ',' { COMMA }
| '*' {KLEENE}
| ';' { SIMI }
| '"'      { read_string (Buffer.create 17) lexbuf }
| "//" { read_single_line_comment lexbuf }
| "(*" { read_multi_line_comment lexbuf }

| "true" { TRUEToken }
| "false" { FALSEToken }
| '?' {QUESTION}
| "/\\" {CONJ}
| "emp" { EMPTY } 

| '#' { SHARP }
| '^' { POWER } 
| '~' {NEGATION}

| "\\/" {DISJ}
| '!' {LTLNOT}
| '[' { LBrackets }
| ']' { RBrackets }
| '~' {NEGATION}
| float { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }

| "|-" {ENTIL}

| "/*@" {LSPEC}
| "@*/" {RSPEC}
| "/\\" {CONJ}

| '?' {QUESTION}
| '#' { SHARP }


| "||" { PAR }
| "require" {REQUIRE}
| "ensure" {ENSURE}

| "hiphop" {HIPHOP}
| "inout" {INOUT}
| "out" {OUT}
| "end" {END}
| "in" {IN}

| "when" {WHEN}

| "count" { COUNT }
| "abort" {ABORT} 
| "halt" { NOTHING }
| "yield" {PAUSE}  
| "loop" {LOOP}
| "signal" {SIGNAL}
| "emit" {EMIT}
| "await" {AWAIT}
| "async" {ASYNC}

| "assert" {ASSERT}

| "present" {PRESENT}
| "run" {RUN}
| "trap" {TRAP}
| "exit" {EXIT}
| "emp" { EMPTY }

| "else" {ELSE}
| "[]" {GLOBAL}
| "include" {INCLUDE}
| '"' { read_string (Buffer.create 17) lexbuf }

*)
