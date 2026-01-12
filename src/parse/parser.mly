%{
open Core.Syntax
open Bindlib

(** Resolve an identifier when parsing:
    - If the identifier is bound, then it's a variable.
    - Otherwise, we assume that it is a symbol.

    In the future, we may maintain a symbol table for the parser,
    if we have multiple kind of symbols. *)
let resolve_identifier x =
  match Binders.get_opt x with
  | None -> Symbol {sym_name = x}
  | Some v -> Var v
%}

%token EQUAL
%token GREATER
%token LESS
%token PLUS
%token MINUS
%token STAR
%token STARDOT
%token MINUSGREATER
%token EQUALGREATER
%token DOT
%token TILDE
%token SUBSUMES
%token CONJUNCTION
%token DISJUNCTION
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token SEMI
%token COMMA
%token DOLLAR

%token TRUE
%token FALSE
%token EMP

%token <int> INT
%token <string> STRING
%token <string> LOWERCASE_IDENT
%token <string> CAPITAL_IDENT

%token EXISTS
%token FORALL
%token REQUIRES
%token ENSURES
%token RETURN
%token LET
%token IN
%token FUN
%token SHIFT
%token RESET
%token LONGARROW
%token COLONCOLON

%token EOF

///////////////////////////

// in increasing order of precedence
%nonassoc SUBSUMES
%nonassoc FUN
%nonassoc REQUIRES ENSURES
%nonassoc FORALL EXISTS // lower than ;
%right DISJUNCTION
%right SEMI

// term
%nonassoc EQUAL
%nonassoc MINUSGREATER
%nonassoc GREATER
%nonassoc LESS
%right EQUALGREATER
%left CONJUNCTION

// term
%right STAR

// term
%left PLUS //MINUS
%left STARDOT // multiplication
%right COLONCOLON
// %nonassoc TILDE
// %nonassoc DOT
// %nonassoc IN

%start parse_term
%type <term> parse_term
%start parse_decl
%type <decl> parse_decl
// %start parse_lemma
// %type <Hiptypes.lemma> parse_lemma
%%

%inline bin_op:
  | GREATER EQUAL
      { Ge }
  | LESS EQUAL
      { Lt }
  | GREATER
      { Gt }
  | LESS
      { Lt }
  | EQUAL
      { Eq }
  | PLUS
      { Plus }
  | STARDOT
      { Times }
  | COLONCOLON
      { Cons }
;

// %inline bin_term_op:
//   | MINUS
//       { Minus }
//   | PLUS PLUS
//       { SConcat }
//   | STARDOT
//       { TTimes }
// ;

// const:
//   | LPAREN RPAREN
//       { ValUnit }
//   | TRUE
//       { TTrue }
//   | FALSE
//       { TFalse }
//   | s = STRING
//       { TStr s }
// ;

// these terms cannot contain staged logic sequencing
term2:
  | LPAREN RPAREN
      { Unit }

  | n = INT
      { Int n }

  | TRUE
      { True }

  | FALSE
      { False }

  | x=LOWERCASE_IDENT
      { resolve_identifier x }

  | t1=term2 op=bin_op t2=term2
      { Binop (op, t1, t2) }

  | LBRACKET RBRACKET
      { Nil }

  | LBRACKET items=separated_nonempty_list(SEMI, term2) RBRACKET
      { List.fold_right (fun v t -> Binop (Cons, v, t)) items Nil }

  | LPAREN
  // items=separated_nonempty_list(COMMA, term2)
  items=tuple_content
  RPAREN
      { Tuple items }

  | LPAREN s=term0 RPAREN
      { s }

  | //LPAREN
  FUN xs=binders MINUSGREATER s=term2 %prec FUN //RPAREN
    { let xs = Binders.remove_all xs in
      Fun (unbox (bind_mvar xs (box_term s))) }

  | p1 = term2 CONJUNCTION p2 = term2
    { Conj (p1, p2) }

  | p1 = term2 EQUALGREATER p2 = term2
    { Implies (p1, p2) }

  | a = term2 SUBSUMES b = term2
    { Subsumes (a, b) }

  | EMP
      { Emp }

  | l=term2 MINUSGREATER v=term2
      { PointsTo (l, v) }

  | k1 = term2 STAR k2 = term2
      { SepConj (k1, k2) }

  | s1 = term2 DISJUNCTION s2 = term2
      { Disj (s1, s2) }

  | REQUIRES h = term2
      { Requires h }

  | ENSURES h = term2
      { Ensures h }

  // // | f=term2 arg=term2+
  // | f=term2 arg=nonempty_list(term2)
  //   { Apply (f, arg) }

  | RESET LPAREN s=term2 RPAREN
      { Reset s }

  | FORALL xs = binders DOT
    s = term2 %prec FORALL
      { let xs = Binders.remove_all xs in
        Forall (unbox (bind_mvar xs (box_term s))) }

  | EXISTS xs = binders DOT
    s = term2 %prec EXISTS
      { let xs = Binders.remove_all xs in
        Exists (unbox (bind_mvar xs (box_term s))) }
  ;

term1:
  | f=term2 arg=nonempty_list(term2)
    { Apply (f, arg) }
  | t=term2
      { t }
  ;

term0:
  | t=term1
      { t }

  | s1=term0 SEMI s2=term0
      { Sequence (s1, s2) }

  | s1=term0 SEMI x=binder DOT s2=term0 %prec SEMI
      {
        let x = Binders.remove x in
        (* TODO quadratic, possibly return a box from the rules *)
        Bind (s1, unbox (bind_var x (box_term s2))) }

;


tuple_content:
  | e1=term0 COMMA e2=term0
    { [e1; e2] }
  | e1=term0 COMMA rest=tuple_content
    { e1::rest }
  ;
  // items=separated_nonempty_list(COMMA, term1)

//   | TILDE t = term
//       { TNot t }
  // | t1 = term op = bin_rel_op t2 = term
//       { Rel (op, t1, t2) }

  // | v=LOWERCASE_IDENT DOLLAR LPAREN args=separated_list(COMMA, term) RPAREN
  //     { App (v, args) }

//   | v = CAPITAL_IDENT
//       { Construct (v, []) }
//   | v = CAPITAL_IDENT LPAREN args = separated_list(COMMA, term) RPAREN
//       { Construct (v, args) }

  // | f=LOWERCASE_IDENT items=delimited(LPAREN, separated_nonempty_list(COMMA, term), RPAREN)
  //     { TApp (f, items) }

  // | SHIFT LPAREN v = LOWERCASE_IDENT DOT s = term RPAREN
  //     { (* TODO: shiftc *)
  //       let x = Variables.fresh_variable ~v:"x" "continuation argument" in
  //       Shift (true, v, s, x, NormalReturn (Atomic (EQ, Variables.res_var, Var x), EmptyHeap)) }

// fn:
//   | v = LOWERCASE_IDENT LPAREN args = separated_list(COMMA, term) RPAREN
//     { (v, args) }
// ;

  // | RETURN t = term
  //     { Return t }

//   // these cause shift-reduce conflicts, are not used, and are not in the symbolic heap fragment
// //   | p1 = term DISJUNCTION p2 = term
// //       { Or (p1, p2) }
//   // | pure_formula IMPLICATION pure_formula { Imply ($1, $3) }
//   | TILDE p = term
//       { Not p }
// //   | v = LOWERCASE_IDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, pure_formula_term), RPAREN) { Predicate (v, args) }
//   | p = delimited(LPAREN, term, RPAREN)
//       { p }

def:
  | xs = binders EQUAL s = term0
    { let xs = Binders.remove_all xs in
      unbox (bind_mvar xs (box_term s)) }

symbol:
  | x = LOWERCASE_IDENT
    { {sym_name = x} }

binders:
  | xs=LOWERCASE_IDENT+
    {
      List.iter Binders.create xs
      ; xs
    }

binder:
  | x=LOWERCASE_IDENT
    {
      Binders.create x; x
    }
      // Binders.push_scope (); x

// lemma:
//   | name_params=fn EQUAL lhs=term LONGARROW rhs=term
//     { let (f, params) = name_params in
//       let params =
//         List.map (function Var s -> s | _ -> failwith "invalid lemma") params
//       in
//       { l_name = f;
//         l_params = params;
//         l_left = lhs;
//         l_right = rhs }
//     }
// ;

parse_term:
  | t = term0 EOF
      { t }

// at the moment, the only declaration we may have is function declaration.
parse_decl:
  | sym = symbol def = def EOF
    { Dfun (sym, def) }

// parse_lemma:
//   | t = lemma EOF
//       { t }
