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
%token <string> UIDENT
%token <string> INT
%token TRUE SHIFT RESET LAMBDA REQUIRE SHARP LANG DEFINE FALSE FUN LET IF GET SET
%token LPAREN RPAREN LBRACKET RBRACKET SLASH AMPERAMPER SEMI COMMA 
%token LSPECCOMMENT RSPECCOMMENT DISJUNCTION CONJUNCTION STAR
%token PLUS  MINUS  MINUSGREATER EQUAL BANG  LESSTHENEQUAL GREATERTHENEQUAL LESSTHEN GREATERTHEN
%token POWER TILDE PROP_TRUE  PROP_FALSE EXISTS REQUIRES ENSURES SUBSUMES EMP LBRACE RBRACE BAR
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
| EQUAL {"="}

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


| SEMI LSPECCOMMENT ef=disj_effect_spec RSPECCOMMENT 
  LPAREN DEFINE signature=fun_signature m_body=core_lang RPAREN prog=prog {
  let (m_name, m_params) = signature in 

  let new_meth = Meth (m_name, m_params, Some ef, m_body, [], None) in 
  new_meth :: prog

}

effect_trace_value:
  | pure_formula_term {$1}
;

pure_formula_term:
  | n = INT { let i = n in Num (int_of_string i) }
  | elts=delimited(LBRACKET, separated_list(SEMI, effect_trace_value), RBRACKET)
    //{TList (List.map (fun a -> Num a) n)}
    // turn this into a cascade of conses, like ocaml does, for simplicity
    { List.fold_right (fun c t -> TCons (c, t)) elts Nil }

  | LPAREN RPAREN {UNIT}
  // | LPAREN n = list_of_TupleTerms RPAREN {TTupple n}


  | MINUS {Var "_"}
  | constr=LIDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, pure_formula_term), RPAREN) { TApp (constr, args) }
  | v = LIDENT { Var v }
  (*| pure_formula_term rest = pure_formula_term_aux { 
    let (op, t) = rest in 
    if String.compare op "+" == 0 then Plus ($1, t) 
    *)

    
  | TRUE { TTrue }
  | FALSE { TFalse }

  // | LBRACKET RBRACKET { Nil }
  // | pure_formula_term COLONCOLON pure_formula_term { TCons ($1, $3) }
  // TODO [1; ...]

  | pure_formula_term PLUS pure_formula_term { Plus ($1, $3) }

  | pure_formula_term MINUS pure_formula_term { Minus ($1, $3) }
  | pure_formula_term AMPERAMPER pure_formula_term { TAnd ($1, $3) }
  | LPAREN pure_formula_term POWER LPAREN pure_formula_term RPAREN RPAREN { TPower ($2, $5) }
  

  | LPAREN pure_formula_term RPAREN { $2 }

  (*
  | LPAREN FUN params=nonempty_list(LIDENT) LSPECCOMMENT ef=disj_effect_spec RSPECCOMMENT b=ioption(preceded(MINUSGREATER, expr)) RPAREN
    { TLambda (Pretty.verifier_getAfreeVar "plambda", params, ef, Option.map (Core_lang.transformation []) b) }
    *)
;

pure_formula: 
  | PROP_TRUE { True }
  | PROP_FALSE { False }
  | a = pure_formula_term LESSTHEN b = pure_formula_term { Atomic (LT, a, b) }
  | a = pure_formula_term GREATERTHEN b = pure_formula_term { Atomic (GT, a, b) }
  | a = pure_formula_term EQUAL b = pure_formula_term { Atomic (EQ, a, b) }
  | a = pure_formula_term SUBSUMES b = pure_formula_term { Subsumption (a, b) }

  | a = pure_formula_term op = GREATERTHENEQUAL b = pure_formula_term {Atomic (GTEQ, a, b)}
  | a = pure_formula_term op = LESSTHENEQUAL b = pure_formula_term {Atomic (LTEQ, a, b)}

  | pure_formula CONJUNCTION pure_formula { And ($1, $3) }
  // these cause shift-reduce conflicts, are not used, and are not in the symbolic heap fragment
  // | pure_formula DISJUNCTION pure_formula { Or ($1, $3) }
  // | pure_formula IMPLICATION pure_formula { Imply ($1, $3) }
  | TILDE pure_formula { Not ($2) } 
  | v = LIDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, pure_formula_term), RPAREN) { Predicate (v, args) }
;


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

stagedSpecArgs :
  | s=statefml COMMA rest=separated_nonempty_list(COMMA, effect_trace_value) { (fst s, snd s, rest) }
  | s=statefml { (fst s, snd s, []) }


stagedSpec1 : 
  | EXISTS vs=nonempty_list(LIDENT) { Exists vs }
  | REQUIRES f=statefml {
      let (p, h) = f in
      Require (p, h)
    }
  | ENSURES f=statefml {
      let (p, h) = f in
      (*
      let (p1, r) = Pretty.split_res p in
      let r =
        match r with
        | [] -> UNIT
        | [x] -> x
        | _ -> failwith "too many res bindings"
      in
      *)
      NormalReturn (p, h)
    }
  | constr=UIDENT args=delimited(LPAREN, stagedSpecArgs, RPAREN)
  {
    match constr, args with
    | "Norm", (p, h, []) -> NormalReturn (p, h)
    | "Norm", (p, h, [r]) ->
      (* backward compat *)
      NormalReturn (And (res_eq r, p), h)
    | "Norm", (p, h, _) -> failwith "norm cannot have more than 2 args"
    | _, (p, h, a) ->
      let init, last = unsnoc a in
      RaisingEff (p, h, (constr, init), last)
  }
  | constr=LIDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, effect_trace_value), RPAREN)
  {
    (* INFIXOP0 *)
    (* we don't check if the infix op is a dollar *)
    let init, last = unsnoc args in
    HigherOrder (True, EmptyHeap, (constr, init), last)
  }


effect_spec:
| s=separated_nonempty_list(SEMI, stagedSpec1) { s }

disj_effect_spec:
| d=separated_nonempty_list(DISJUNCTION, effect_spec) { d }

