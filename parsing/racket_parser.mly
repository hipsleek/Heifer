%{ 
open Hipcore
open Hiptypes 

let getAnewBinder () = 
    let correntCounter = !counter_4_inserting_let_bindings in 
    let newBinder = "x" ^ string_of_int correntCounter in 
    let () = counter_4_inserting_let_bindings :=correntCounter +1 in 
    newBinder


%}

%token <string> STRING
%token <string> LIDENT 
%token <string> INT
%token TRUE SHIFT RESET LAMBDA REQUIRE SHARP LANG DEFINE FALSE FUN LET IF GET SET
%token LPAREN RPAREN LBRACKET RBRACKET SLASH AMPERAMPER SEMI COMMA 
%token LSPECCOMMENT RSPECCOMMENT DISJUNCTION CONJUNCTION STAR
%token PLUS  MINUS  MINUSGREATER EQUAL BANG  LESSTHENEQUAL GREATERTHENEQUAL LESSTHEN GREATERTHEN
%token EOF
%start <Hiptypes.intermediate list> prog
%type <string list> params
%type <string> rec_path
%type <Hiptypes.core_lang> core_lang
%type <(string * string list) > fun_signature
%type <Hiptypes.core_value > core_value
%type <Hiptypes.core_value list> core_values
%type <Hiptypes.core_lang list> expre_list


%%
ident:
| s = LIDENT {s} 
| s = LIDENT BANG {s^"!"} 
| s1 = LIDENT MINUSGREATER s2 = LIDENT {s1^"->"^s2} 
| s1 = LIDENT MINUS s2 = LIDENT {s1^"-"^s2} 
| PLUS {"+"}
| MINUS {"-"}
| LESSTHENEQUAL {"<="}
| GREATERTHENEQUAL {">="}
| LESSTHEN {"<"}
| GREATERTHEN {">"}


params:
| {[]}
| s=ident rest = params {s :: rest}

core_values:
| {[]}
| s=core_value rest = core_values {s :: rest}

expre_list:
| s1=core_lang s2=core_lang {[s1;s2]}
| s=core_lang rest = expre_list {s :: rest}


sequencing:
| s=core_lang {[s]}
| LPAREN s=core_lang RPAREN rest = sequencing {s :: rest}


fun_signature: 
| LPAREN nm= ident params=params RPAREN {(nm, params)}
| LPAREN nm= GET params=params RPAREN {("get!", params)}



core_value:
  | n = INT { Num (int_of_string n) }
  | LPAREN RPAREN {UNIT}
  | v = ident { Var v }
  | v = STRING { TStr v }
  | TRUE { TTrue }
  | FALSE { TFalse }
  | core_value AMPERAMPER core_value { TAnd ($1, $3) }
  | LPAREN core_value RPAREN { $2 }



let_binding: 
| {[]}
| LBRACKET nm=ident expr=core_lang RBRACKET rest = let_binding  {(nm, expr):: rest}



core_lang: 
| v=core_value {CValue v}
| GET id=ident {CRead id}
| SET id=ident m_body=core_lang {
  match m_body with 
  | CValue v -> CWrite (id, v)
  | _-> 
    let newBinder = getAnewBinder () in 
    CLet (newBinder, m_body, CWrite (id, Var newBinder ) )

  
  }


| IF cond=core_lang thenB=core_lang elseB=core_lang {
    

  match cond with 
  | CValue v -> CIfELse (Atomic(EQ, v, TTrue ), thenB, elseB)
  | _ -> 
    let newBinder = getAnewBinder () in 
    let if_else = CIfELse (Atomic(EQ, Var newBinder, TTrue ), thenB, elseB) in 
    CLet(newBinder, cond, if_else)




  
}
| LAMBDA LPAREN params=params RPAREN m_body=core_lang {CLambda (params, None, m_body)}
| list_of_expression =expre_list 
  {
  match list_of_expression with 
  | head :: tail -> 
    
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
    
| SHIFT nm=ident m_bodys=sequencing {
  let rec compose body_list = 
    match body_list with 
    | [x] -> x
    | x :: xs -> CLet ("_", x, compose xs)
  in 
  CShift(nm, compose m_bodys)
  
  }
| LET LPAREN letbinding=let_binding RPAREN m_bodys=sequencing {
  let rec compose_body m_bodys = 
    match m_bodys with 
    | [x] -> x
    | x :: xs -> CLet ("_", x, compose_body xs)
  in 

  let m_body = compose_body m_bodys in 


  let rec compose li =
    match li with 
    | [(nm, expr)] -> CLet (nm, expr, m_body)
    | (nm, expr) :: rest -> CLet (nm, expr, compose rest)
  in 
  compose letbinding
  
}
| RESET m_body=core_lang {(CReset(m_body))}
| LPAREN expr=core_lang RPAREN {expr}






rec_path:
| s= ident {s}
| s= ident SLASH rest=rec_path {s^"/"^rest}

prog:
| SHARP LANG rec_path prog=prog {prog} (* this is an imcomplete parsing for "#lang racket" *)
| LPAREN REQUIRE rec_path RPAREN prog=prog { prog } 



| LPAREN DEFINE signature=fun_signature m_body=core_lang RPAREN prog=prog {
  let (m_name, m_params) = signature in 

  let new_meth = Meth (m_name, m_params, None, m_body, [], None) in 
  new_meth :: prog

}

| LPAREN DEFINE nm=ident m_body=core_value RPAREN prog=prog {
  let (m_name, m_params) = ("main", []) in 
  let m_body' = CLet (nm, CRef m_body , CValue (Var nm) ) in 
  let new_meth = Meth (m_name, m_params, None, m_body', [], None) in 
  new_meth :: prog}

| LPAREN m_body=core_lang RPAREN prog=prog { 
  let (m_name, m_params) = ("main", []) in 
  let new_meth = Meth (m_name, m_params, None, m_body, [], None) in 
  new_meth :: prog}
| EOF {[]} 

(*
| SEMI LSPECCOMMENT ef=disj_effect_spec RSPECCOMMENT 
  LPAREN DEFINE signature=fun_signature m_body=core_lang RPAREN prog=prog {
  let (m_name, m_params) = signature in 

  let new_meth = Meth (m_name, m_params, Some ef, m_body, [], None) in 
  new_meth :: prog

}

statefml:
  | h=heapkappa { (True, h) }
  | p=pure_formula CONJUNCTION h=heapkappa { (p, h) }
  | h=heapkappa CONJUNCTION p=pure_formula { (p, h) }
  | p=pure_formula { (p, EmptyHeap) }


heapkappa:
| EMP { EmptyHeap }
| str=ident MINUSGREATER args = pure_formula_term
  { PointsTo(str, args) }
| a=heapkappa STAR b=heapkappa
  { SepConj(a, b) }

stagedSpec1 : 
  | EXISTS vs=nonempty_list(ident) { Exists vs }
  | REQUIRES f=statefml {
      let (p, h) = f in
      Require (p, h)
    }
  

effect_spec:
| s=separated_nonempty_list(SEMI, stagedSpec1) { s }

disj_effect_spec:
| d=separated_nonempty_list(DISJUNCTION, effect_spec) { d }

*)