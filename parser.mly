%{ open Ast %}
%{ open List %}

%token <string> STRING

%token <int> INTE

(*
%token <string> VAR 
%token  LPAR RPAR SIMI  COMMA LBRACK RBRACK      
%token  MINUS PLUS   
%token EOF GT LT EQ  GTEQ LTEQ   CONCAT 
%token VARKEY KLEENE NEW HIPHOP MODULE IN OUT 
%token EMIT AWAIT DO EVERY FORK PAR LOOP YIELD ABORT SIGNAL
%token IF HALT CONST LET HOP FUNCTION ASYNC IMPLY 
%token RETURN BREAK COLON ELSE TRY CATCH RUN
%token REQUIRE ENSURE  LSPEC RSPEC
*)

%token EOF

%start program
%type <(Ast.expression) list> program


%%

program:
| EOF {[]}
| a = expression r = program { append [a] r }

literal: 
| n = INTE {INT n}
| str = STRING {STRING str}


expression:
| l = literal {Literal l }
