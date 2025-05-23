%{
open Hipcore
open Hiptypes
%}

%token MINUSGREATER
%token DOT
%token EQUAL
%token TILDE
%token STAR
%token CONJUNCTION
%token DISJUNCTION
%token LPAREN
%token RPAREN

%token <int> INT
%token <string> IDENT

%token TRUE
%token FALSE
%token EMP

%token EXISTS
%token REQUIRES
%token ENSURES
%token SEMICOLON
%token LET
%token IN
%token SHIFT
%token RESET

%token EOF

%nonassoc TILDE
%right STAR
%right CONJUNCTION
%right DISJUNCTION

%right SEMICOLON
%nonassoc DOT
%nonassoc IN

%start parse_pi
%type <Hiptypes.pi> parse_pi
%start parse_kappa
%type <Hiptypes.kappa> parse_kappa
%start parse_staged_spec
%type <Hiptypes.staged_spec> parse_staged_spec
%%

const:
  | LPAREN RPAREN
      { ValUnit }
  | n = INT
      { Num n }
  | TRUE
      { TTrue }
  | FALSE
      { TFalse }
;
term:
  | c = const
      { Const c }
;
pi:
  | TRUE
      { True }
  | FALSE
      { False }
  // | a = pure_formula_term LESS b = pure_formula_term { Atomic (LT, a, b) }
  // | a = pure_formula_term GREATER b = pure_formula_term { Atomic (GT, a, b) }
  // | a = pure_formula_term EQUAL b = pure_formula_term { Atomic (EQ, a, b) }
  // | a = pure_formula_term SUBSUMES b = pure_formula_term { Subsumption (a, b) }

  // | a = pure_formula_term op = INFIXOP0 b = pure_formula_term
  // {
  //   let op =
  //     match op with
  //     | "<=" -> LTEQ
  //     | ">=" -> GTEQ
  //     | _ -> failwith ("unexpected infix operator " ^ op)
  //   in
  //   Atomic (op, a, b)
  // }
  | p1 = pi CONJUNCTION p2 = pi
      { And (p1, p2) }
  // these cause shift-reduce conflicts, are not used, and are not in the symbolic heap fragment
  // | pure_formula DISJUNCTION pure_formula { Or ($1, $3) }
  // | pure_formula IMPLICATION pure_formula { Imply ($1, $3) }
  | TILDE p = pi
      { Not p } 
  // | v = IDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, pure_formula_term), RPAREN) { Predicate (v, args) }
;
kappa:
  | EMP
      { EmptyHeap }
  | v = IDENT MINUSGREATER t = term
      { PointsTo (v, t) }
  | k1 = kappa STAR k2 = kappa
      { SepConj (k1, k2) }
;
state:
  | p = pi
      { (p, EmptyHeap) }
  | k = kappa
      { (True, k) }
  | p = pi CONJUNCTION k = kappa
      { (p, k) }
  | k = kappa CONJUNCTION p = pi
      { (p, k) }
;
staged_spec:
  | EXISTS v = IDENT DOT s = staged_spec
      { Exists (v, s) }
  | REQUIRES s = state
      { let (p, k) = s in Require (p, k) }
  | ENSURES s = state
      { let (p, k) = s in NormalReturn (p, k) }
  | v = IDENT (* TODO *)
      { HigherOrder (v, []) }
  | SHIFT LPAREN v = IDENT DOT s = staged_spec RPAREN
      { Shift (true, v, s) }
  | RESET LPAREN s = staged_spec RPAREN
      { Reset s }
  | s1 = staged_spec SEMICOLON s2 = staged_spec
      { Sequence (s1, s2) }
  | LET v = IDENT EQUAL s1 = staged_spec IN s2 = staged_spec
      { Bind (v, s1, s2) }
  | s1 = staged_spec DISJUNCTION s2 = staged_spec
      { Disjunction (s1, s2) }
;
parse_pi:
  | p = pi EOF
      { p }
;
parse_kappa:
  | k = kappa EOF
      { k }
;
parse_staged_spec:
  | s = staged_spec EOF
      { s }
