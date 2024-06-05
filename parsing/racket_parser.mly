%{ 
open Hipcore
open Hiptypes 
%}

%token <string> LVAR 
%token TRUE SHIFT RESET LAMBDA REQUIRE SHARP LANG DEFINE
%token LPAR RPAR LBrackets RBrackets SLASH
%token EOF
%start <Hiptypes.core_program> prog
%type <string list> params
%type <string> rec_path
%type <Hiptypes.core_lang> core_lang
%type <(string * string list) > fun_signature

%%


params:
| {[]}
| s=LVAR rest = params {s :: rest}


fun_signature: 
| LPAR nm= LVAR params=params RPAR {(nm, params)}

core_lang: 
| TRUE {CValue TTrue}

rec_path:
| s= LVAR {s}
| s= LVAR SLASH rest=rec_path {s^"/"^rest}

prog:
| SHARP LANG rec_path prog=prog {prog} (* this is an imcomplete parsing for "#lang racket" *)
| LPAR REQUIRE rec_path RPAR prog=prog { prog } 
| LPAR DEFINE signature=fun_signature LPAR m_body=core_lang RPAR RPAR prog=prog {
  let (m_name, m_params) = signature in 
  let new_meth = {m_name= m_name; m_params= m_params; m_spec= None; m_body= m_body; m_tactics=[]} in 
  {prog with cp_methods=prog.cp_methods @ [new_meth]}}
| EOF {empty_program}
