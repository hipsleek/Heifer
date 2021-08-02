
let string_of_token =
  let open Parser in
  function
  | AMPERAMPER -> "AMPERAMPER"
  | AMPERSAND -> "AMPERSAND"
  | AND -> "AND"
  | AS -> "AS"
  | ASSERT -> "ASSERT"
  | BACKQUOTE -> "BACKQUOTE"
  | BANG -> "BANG"
  | BAR -> "BAR"
  | BARBAR -> "BARBAR"
  | BARRBRACKET -> "BARRBRACKET"
  | BEGIN -> "BEGIN"
  (* | <char> CHAR -> <char> "CHAR" *)
  | CLASS -> "CLASS"
  | COLON -> "COLON"
  | COLONCOLON -> "COLONCOLON"
  | COLONEQUAL -> "COLONEQUAL"
  | COLONGREATER -> "COLONGREATER"
  | COMMA -> "COMMA"
  | CONSTRAINT -> "CONSTRAINT"
  | DO -> "DO"
  | DONE -> "DONE"
  | DOT -> "DOT"
  | DOTDOT -> "DOTDOT"
  | DOWNTO -> "DOWNTO"
  | EFFECT -> "EFFECT"
  | ELSE -> "ELSE"
  | END -> "END"
  | EOF -> "EOF"
  | EQUAL -> "EQUAL"
  | EXCEPTION -> "EXCEPTION"
  | EXTERNAL -> "EXTERNAL"
  | FALSE -> "FALSE"
  (* | <string * char option> FLOAT -> <string * char option> "FLOAT" *)
  | FOR -> "FOR"
  | FUN -> "FUN"
  | FUNCTION -> "FUNCTION"
  | FUNCTOR -> "FUNCTOR"
  | REQUIRES -> "REQUIRES"
  | ENSURES -> "ENSURES"
  | EMP -> "EMP"
  | GREATER -> "GREATER"
  | GREATERRBRACE -> "GREATERRBRACE"
  | GREATERRBRACKET -> "GREATERRBRACKET"
  | IF -> "IF"
  | IN -> "IN"
  | INCLUDE -> "INCLUDE"
  (* | <string> INFIXOP0 -> <string> "INFIXOP0" *)
  (* | <string> INFIXOP1 -> <string> "INFIXOP1" *)
  (* | <string> INFIXOP2 -> <string> "INFIXOP2" *)
  (* | <string> INFIXOP3 -> <string> "INFIXOP3" *)
  (* | <string> INFIXOP4 -> <string> "INFIXOP4" *)
  (* | <string> DOTOP -> <string> "DOTOP" *)
  (* | <string> LETOP -> <string> "LETOP" *)
  (* | <string> ANDOP -> <string> "ANDOP" *)
  | INHERIT -> "INHERIT"
  | INITIALIZER -> "INITIALIZER"
  (* | <string * char option> INT -> <string * char option> "INT" *)
  (* | <string> LABEL -> <string> "LABEL" *)
  | LAZY -> "LAZY"
  | LBRACE -> "LBRACE"
  | LBRACELESS -> "LBRACELESS"
  | LBRACKET -> "LBRACKET"
  | LBRACKETBAR -> "LBRACKETBAR"
  | LBRACKETLESS -> "LBRACKETLESS"
  | LBRACKETGREATER -> "LBRACKETGREATER"
  | LBRACKETPERCENT -> "LBRACKETPERCENT"
  | LBRACKETPERCENTPERCENT -> "LBRACKETPERCENTPERCENT"
  | LESS -> "LESS"
  | LESSMINUS -> "LESSMINUS"
  | LET -> "LET"
  | LIDENT _i ->
    (* Format.sprintf "LIDENT %s" i *)
    "LIDENT"
  | LPAREN -> "LPAREN"
  | LBRACKETAT -> "LBRACKETAT"
  | LBRACKETATAT -> "LBRACKETATAT"
  | LBRACKETATATAT -> "LBRACKETATATAT"
  | MATCH -> "MATCH"
  | METHOD -> "METHOD"
  | MINUS -> "MINUS"
  | MINUSDOT -> "MINUSDOT"
  | MINUSGREATER -> "MINUSGREATER"
  | MODULE -> "MODULE"
  | MUTABLE -> "MUTABLE"
  | NEW -> "NEW"
  | NONREC -> "NONREC"
  | OBJECT -> "OBJECT"
  | OF -> "OF"
  | OPEN -> "OPEN"
  (* | <string> OPTLABEL -> <string> "OPTLABEL" *)
  | OR -> "OR"
  (* | PARSER -> "PARSER" *)
  | PERCENT -> "PERCENT"
  | PLUS -> "PLUS"
  | PLUSDOT -> "PLUSDOT"
  | PLUSEQ -> "PLUSEQ"
  (* | <string> PREFIXOP -> <string> "PREFIXOP" *)
  | PRIVATE -> "PRIVATE"
  | QUESTION -> "QUESTION"
  | QUOTE -> "QUOTE"
  | RBRACE -> "RBRACE"
  | RBRACKET -> "RBRACKET"
  | REC -> "REC"
  | RPAREN -> "RPAREN"
  | SEMI -> "SEMI"
  | SEMISEMI -> "SEMISEMI"
  | HASH -> "HASH"
  (* | <string> HASHOP -> <string> "HASHOP" *)
  | SIG -> "SIG"
  | STAR -> "STAR"
  (* | <string * Location.t * string option> STRING -> <string * Location.t * string option> "STRING" *)
  (* |   <string * Location.t * string * Location.t * string option> QUOTED_STRING_EXPR ->   <string * Location.t * string * Location.t * string option> "QUOTED_STRING_EXPR" *)
  (* |   <string * Location.t * string * Location.t * string option> QUOTED_STRING_ITEM ->   <string * Location.t * string * Location.t * string option> "QUOTED_STRING_ITEM" *)
  | STRUCT -> "STRUCT"
  | THEN -> "THEN"
  | TILDE -> "TILDE"
  | TO -> "TO"
  | TRUE -> "TRUE"
  | TRY -> "TRY"
  | TYPE -> "TYPE"
  (* | <string> UIDENT -> <string> "UIDENT" *)
  | UNDERSCORE -> "UNDERSCORE"
  | VAL -> "VAL"
  | VIRTUAL -> "VIRTUAL"
  | WHEN -> "WHEN"
  | WHILE -> "WHILE"
  | WITH -> "WITH"
  (* | <string * Location.t> COMMENT -> <string * Location.t> "COMMENT" *)
  (* | <Docstrings.docstring> DOCSTRING -> <Docstrings.docstring> "DOCSTRING" *)
  | EOL -> "EOL"
  | _ -> "unimplemented"
