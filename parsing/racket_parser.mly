%{ 
open Hipcore
open Hiptypes 
%}

%token <string> LIDENT 
%token <string> INT
%token TRUE SHIFT RESET LAMBDA REQUIRE SHARP LANG DEFINE FALSE FUN
%token LPAREN RPAREN LBRACKET RBRACKET SLASH AMPERAMPER MINUSGREATER MINUS SEMI COMMA PLUS LSPECCOMMENT RSPECCOMMENT
%token EOF
%start <Hiptypes.core_program> prog
%type <string list> params
%type <string> rec_path
%type <Hiptypes.core_lang> core_lang
%type <(string * string list) > fun_signature
%type <Hiptypes.core_value > core_value
%type <Hiptypes.core_value list> core_values


%%


params:
| {[]}
| s=LIDENT rest = params {s :: rest}

core_values:
| {[]}
| s=core_value rest = core_values {s :: rest}


fun_signature: 
| LPAREN nm= LIDENT params=params RPAREN {(nm, params)}



core_value:
  | n = INT { Num (int_of_string n) }

  | LPAREN RPAREN {UNIT}
  // | LPAREN n = list_of_TupleTerms RPAREN {TTupple n}


  | MINUS {Var "_"}
  | constr=LIDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, core_value), RPAREN) { TApp (constr, args) }
  | v = LIDENT { Var v }
  (*| core_value rest = core_value_aux { 
    let (op, t) = rest in 
    if String.compare op "+" == 0 then Plus ($1, t) 
    *)

    
  | TRUE { TTrue }
  | FALSE { TFalse }

  // | LBRACKET RBRACKET { Nil }
  // | core_value COLONCOLON core_value { TCons ($1, $3) }
  // TODO [1; ...]

  | core_value PLUS core_value { Plus ($1, $3) }

  | core_value MINUS core_value { Minus ($1, $3) }
  | core_value AMPERAMPER core_value { TAnd ($1, $3) }



  | LPAREN core_value RPAREN { $2 }

  (*
  | LPAREN FUN params=nonempty_list(LIDENT) LSPECCOMMENT (*ef=disj_effect_spec*) RSPECCOMMENT b=ioption(preceded(MINUSGREATER, core_lang)) RPAREN
    { TLambda (Pretty.verifier_getAfreeVar "plambda", params, (* ef *) [], Option.map (Core_lang.transformation []) b) }
*)



core_lang: 
| LPAREN TRUE RPAREN {CValue TTrue}
| LPAREN LAMBDA LPAREN params=params RPAREN m_body=core_lang RPAREN {CLambda (params, None, m_body)}
| LPAREN nm=LIDENT params=core_values RPAREN {(CFunCall(nm, params))}






rec_path:
| s= LIDENT {s}
| s= LIDENT SLASH rest=rec_path {s^"/"^rest}

prog:
| SHARP LANG rec_path prog=prog {prog} (* this is an imcomplete parsing for "#lang racket" *)
| LPAREN REQUIRE rec_path RPAREN prog=prog { prog } 
| LPAREN DEFINE signature=fun_signature m_body=core_lang RPAREN prog=prog {
  let (m_name, m_params) = signature in 
  let new_meth = {m_name= m_name; m_params= m_params; m_spec= None; m_body= m_body; m_tactics=[]} in 
  {prog with cp_methods=prog.cp_methods @ [new_meth]}}
| EOF {empty_program}
