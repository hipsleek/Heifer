%token TRUE
%token EOF
%start <bool> prog
%%

prog:
  | TRUE { true }
  | EOF { false };
