%{
open Core.Syntax
open Bindlib
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

/////////////////////////////////
// Precedence and associativity

// low precedence
%nonassoc FORALL EXISTS FUN
%right SUBSUMES EQUALGREATER
%left DISJUNCTION
%right SEMI
%nonassoc REQUIRES ENSURES


%nonassoc EQUAL GREATER LESS

%left CONJUNCTION
%left STAR
%nonassoc MINUSGREATER

%left PLUS MINUS
%left STARDOT // multiplication
%right COLONCOLON
%nonassoc TRUE FALSE RESET LPAREN LOWERCASE_IDENT LBRACKET INT EMP
%left APP
// high precedence

/////////////////////////////////

%start parse_term
%type <term> parse_term
%start parse_decl
%type <decl> parse_decl

%%

%inline bin_op:
  | GREATER EQUAL { Ge }
  | LESS EQUAL { Lt }
  | GREATER { Gt }
  | LESS { Lt }
  | EQUAL { Eq }
  | PLUS { Plus }
  | MINUS { Minus }
  | STARDOT { Times }
  | COLONCOLON { Cons }
  ;

// terms which bind more tightly than sequencing
// and don't have sequencing in them
unsequenced_term:
  | LPAREN RPAREN
      { Unit }

  | n=INT
      { Int n }

  | TRUE
      { True }

  | FALSE
      { False }

  | EMP
      { Emp }

  | x=LOWERCASE_IDENT
      { Parser_state.resolve_identifier x }

  | LBRACKET RBRACKET
      { Nil }

  // list literal
  | LBRACKET items=separated_nonempty_list(SEMI, unsequenced_term) RBRACKET
      { List.fold_right (fun v t -> Binop (Cons, v, t)) items Nil }

  // single-element or empty tuplesa are not allowed
  | LPAREN i=term COMMA items=separated_nonempty_list(COMMA, term) RPAREN
      { Tuple (i::items) }

  | f=unsequenced_term arg=unsequenced_term %prec APP
    { Apply (f, [arg]) }

  | t1=unsequenced_term op=bin_op t2=unsequenced_term
      { Binop (op, t1, t2) }

  | REQUIRES h=unsequenced_term
      { Requires h }

  | ENSURES h=unsequenced_term
      { Ensures h }

  | RESET LPAREN s=term RPAREN
      { Reset s }

  | LPAREN s=term RPAREN
      { s }

  | p1=unsequenced_term CONJUNCTION p2=unsequenced_term
    { Conj (p1, p2) }

  | l=unsequenced_term MINUSGREATER v=unsequenced_term
      { PointsTo (l, v) }

  | k1=unsequenced_term STAR k2=unsequenced_term
      { SepConj (k1, k2) }

//   | TILDE t = term
//       { TNot t }

// terms are almost all in a single level, using precedence levels to disambiguate parsing.
// the only tweak is to solve the reduce/reduce conflict from sequencing and lists, by creating an extra level, like what ocaml itself does.
term:
  | s=unsequenced_term
    { s }

  | FUN xs=binders MINUSGREATER s=term %prec FUN
    { let xs = Parser_state.remove_all xs in
      Fun (unbox (bind_mvar xs (box_term s))) }

  | FORALL xs = binders DOT
    s = term %prec FORALL
      { let xs = Parser_state.remove_all xs in
        Forall (unbox (bind_mvar xs (box_term s))) }

  | EXISTS xs = binders DOT
    s = term %prec EXISTS
      { let xs = Parser_state.remove_all xs in
        Exists (unbox (bind_mvar xs (box_term s))) }

  // | SHIFT LPAREN v = LOWERCASE_IDENT DOT s = term RPAREN
  //     { (* TODO: shiftc *)
  //       let x = Variables.fresh_variable ~v:"x" "continuation argument" in
  //       Shift (true, v, s, x, NormalReturn (Atomic (EQ, Variables.res_var, Var x), EmptyHeap)) }

  | s1=term SEMI s2=term
      { Sequence (s1, s2) }

  | s1=term SEMI x=binder DOT s2=term %prec SEMI
      {
        let x = Parser_state.remove x in
        (* TODO quadratic, possibly return a box from the rules *)
        Bind (s1, unbox (bind_var x (box_term s2))) }

  | s1=term DISJUNCTION s2=term
      { Disj (s1, s2) }

  | p1=term EQUALGREATER p2=term
    { Implies (p1, p2) }

  | a=term SUBSUMES b=term
    { Subsumes (a, b) }

def:
  | xs = binders EQUAL s = term
    { let xs = Parser_state.remove_all xs in
      unbox (bind_mvar xs (box_term s)) }

symbol:
  | x = LOWERCASE_IDENT
    { { sym_name = x } }

binders:
  | xs=LOWERCASE_IDENT+
    { List.iter Parser_state.create xs;
      xs }

binder:
  | x=LOWERCASE_IDENT
    { Parser_state.create x; x }

parse_term:
  | t = term EOF
      { Postprocess.postprocess t }

parse_decl:
  | sym = symbol def = def EOF
    { let xs, b = unmbind def in
      let body = unbox (bind_mvar xs (box_term (Postprocess.postprocess b))) in
      Dfun (sym, body) }
