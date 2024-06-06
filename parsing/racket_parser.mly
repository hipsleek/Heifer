%{ 
open Hipcore
open Hiptypes 
%}

%token <string> STRING
%token <string> LIDENT 
%token <string> INT
%token TRUE SHIFT RESET LAMBDA REQUIRE SHARP LANG DEFINE FALSE FUN
%token LPAREN RPAREN LBRACKET RBRACKET SLASH AMPERAMPER MINUS SEMI COMMA PLUS LSPECCOMMENT RSPECCOMMENT
%token EOF
%start <Hiptypes.core_program> prog
%type <string list> params
%type <string> rec_path
%type <Hiptypes.core_lang> core_lang
%type <(string * string list) > fun_signature
%type <Hiptypes.core_value > core_value
%type <Hiptypes.core_value list> core_values
%type <Hiptypes.core_lang list> expre_list


%%


params:
| {[]}
| s=LIDENT rest = params {s :: rest}

core_values:
| {[]}
| s=core_value rest = core_values {s :: rest}

expre_list:
| s1=core_lang s2=core_lang {[s1;s2]}
| s=core_lang rest = expre_list {s :: rest}



fun_signature: 
| LPAREN nm= LIDENT params=params RPAREN {(nm, params)}



core_value:
  | n = INT { Num (int_of_string n) }

  | LPAREN RPAREN {UNIT}

  // | LPAREN n = list_of_TupleTerms RPAREN {TTupple n}


  | MINUS {Var "_"}
  | v = LIDENT { Var v }
  | v = STRING { TStr v }
  (*| core_value rest = core_value_aux { 
    let (op, t) = rest in 
    if String.compare op "+" == 0 then Plus ($1, t) 
    *)

    
  | TRUE { TTrue }
  | FALSE { TFalse }

  // | LBRACKET RBRACKET { Nil }
  // | core_value COLONCOLON core_value { TCons ($1, $3) }
  // TODO [1; ...]

  (*| core_value PLUS core_value { Plus ($1, $3) }
  *)

  | core_value MINUS core_value { Minus ($1, $3) }
  | core_value AMPERAMPER core_value { TAnd ($1, $3) }



  | LPAREN core_value RPAREN { $2 }

  (*
  | LPAREN FUN params=nonempty_list(LIDENT) LSPECCOMMENT (*ef=disj_effect_spec*) RSPECCOMMENT b=ioption(preceded(MINUSGREATER, core_lang)) RPAREN
    { TLambda (Pretty.verifier_getAfreeVar "plambda", params, (* ef *) [], Option.map (Core_lang.transformation []) b) }


*)





core_lang: 
| v=core_value {CValue v}
| LAMBDA LPAREN params=params RPAREN m_body=core_lang {CLambda (params, None, m_body)}
| PLUS p1 = core_lang   p2 = core_lang
| p1 = core_lang PLUS  p2 = core_lang {

    let getAnewBinder () = 
      let correntCounter = !counter_4_inserting_let_bindings in 
      let newBinder = "x" ^ string_of_int correntCounter in 
      let () = counter_4_inserting_let_bindings :=correntCounter +1 in 
      newBinder
    in 

    let rec aux (params:Hiptypes.core_lang list) : 
      (((string * Hiptypes.core_lang) list) * (Hiptypes.core_value list) ) = 
      match params with 
      | [] -> [], [] 
      | param::rest -> 
        let (binder1, formal1) = 
        (match param with 
        | CValue v -> [], [v]
        | _ -> 
          let newBinder = getAnewBinder () in 
          [(newBinder, param)], [((Var newBinder))]
        ) in 
        let (binder2, formal2) = aux rest in 
        (binder1@binder2, formal1@formal2) 

    in 
    let params' = aux [p1;p2] in 
    
    let rec compose (li1, li2) = 
      match li1 with
      | [] -> 
        CFunCall("+", li2)

      | (str, expr) :: rest -> CLet(str, expr, compose (rest, li2))
    in 
    (compose params')



  }
| list_of_expression =expre_list 
  {
  match list_of_expression with 
  | head :: tail -> 
    

    let getAnewBinder () = 
      let correntCounter = !counter_4_inserting_let_bindings in 
      let newBinder = "x" ^ string_of_int correntCounter in 
      let () = counter_4_inserting_let_bindings :=correntCounter +1 in 
      newBinder
    in 

    let rec aux (params:Hiptypes.core_lang list) : 
      (((string * Hiptypes.core_lang) list) * (Hiptypes.core_value list) ) = 
      match params with 
      | [] -> [], [] 
      | param::rest -> 
        let (binder1, formal1) = 
        (match param with 
        | CValue v -> [], [v]
        | _ -> 
          let newBinder = getAnewBinder () in 
          [(newBinder, param)], [((Var newBinder))]
        ) in 
        let (binder2, formal2) = aux rest in 
        (binder1@binder2, formal1@formal2) 

    in 
    let (nm, head_binding) = 
      match head with 
      | CValue (Var v) -> v, []
      | _ -> 
        let newBinder = getAnewBinder () in 
        newBinder, [(newBinder, head)]
    in 

    let params' = aux tail in 
    
    let rec compose (li1, li2) = 
      match li1 with
      | [] -> 
        (match head_binding with 
        | [] -> CFunCall(nm, li2)
        | [(str, expr)] -> CLet(str, expr, CFunCall(nm, li2))  
        )

      | (str, expr) :: rest -> CLet(str, expr, compose (rest, li2))
    in 
    (compose params')}
    
| SHIFT nm=LIDENT m_body=core_lang {(CShift(nm, m_body))}
| RESET m_body=core_lang {(CReset(m_body))}
| LPAREN expr=core_lang RPAREN {expr}






rec_path:
| s= LIDENT {s}
| s= LIDENT SLASH rest=rec_path {s^"/"^rest}

prog:
| SHARP LANG rec_path prog=prog {prog} (* this is an imcomplete parsing for "#lang racket" *)
| LPAREN REQUIRE rec_path RPAREN prog=prog { prog } 
| LPAREN DEFINE signature=fun_signature m_body=core_lang RPAREN prog=prog {
  let (m_name, m_params) = signature in 
  let new_meth = {m_name= m_name; m_params= m_params; m_spec= None; m_body= m_body; m_tactics=[]} in 
  {prog with cp_methods=new_meth::prog.cp_methods}}
| LPAREN m_body=core_lang RPAREN prog=prog { 
  let (m_name, m_params) = ("main", []) in 
  let new_meth = {m_name= m_name; m_params= m_params; m_spec= None; m_body= m_body; m_tactics=[]} in 
  {prog with cp_methods=new_meth::prog.cp_methods}}
| EOF {empty_program} 
