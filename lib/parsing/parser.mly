%{
open Hipcore
open Hiptypes
%}

%token EQUAL
%token GREATER
%token LESS
%token PLUS
%token MINUS
%token STAR
%token STARDOT
%token MINUSGREATER
%token DOT
%token TILDE
%token CONJUNCTION
%token DISJUNCTION
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token SEMI
%token COMMA

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
%token LET
%token IN
%token FUN
%token SHIFT
%token RESET
%token LONGARROW

%token EOF

///////////////////////////

%nonassoc EQUAL
%nonassoc GREATER
%nonassoc LESS
%left STARDOT
%left PLUS
%left MINUS
%right STAR
// %nonassoc MINUSGREATER
%nonassoc TILDE
%right CONJUNCTION

%nonassoc DOT
%right DISJUNCTION
%right SEMI
%nonassoc IN

%start parse_pi
%type <Hiptypes.pi> parse_pi
%start parse_kappa
%type <Hiptypes.kappa> parse_kappa
%start parse_state
%type <Hiptypes.pi * Hiptypes.kappa> parse_state
%start parse_staged_spec
%type <Hiptypes.staged_spec> parse_staged_spec
%start parse_term
%type <Hiptypes.term> parse_term
%start parse_lemma
%type <Hiptypes.lemma> parse_lemma
%%

%inline bin_rel_op:
  | GREATER EQUAL
      { GTEQ }
  | LESS EQUAL
      { LTEQ }
  | GREATER
      { GT }
  | LESS
      { LT }
  | EQUAL
      { EQ }
;

%inline bin_term_op:
  | PLUS PLUS
      { SConcat }
  | PLUS
      { Plus }
  | MINUS
      { Minus }
  | STARDOT
      { TTimes }
;

const:
  | LPAREN RPAREN
      { ValUnit }
  | n = INT
      { Num n }
  | TRUE
      { TTrue }
  | FALSE
      { TFalse }
  | s = STRING
      { TStr s }
;

term:
  | c = const
      { Const c }
  | v = LOWERCASE_IDENT
      { Var v }
  | TILDE t = term
      { TNot t }
  | t1 = term op = bin_rel_op t2 = term
      { Rel (op, t1, t2) }
  | t1 = term op = bin_term_op t2 = term
      { BinOp (op, t1, t2) }
  | v = LOWERCASE_IDENT LPAREN args = separated_list(COMMA, term) RPAREN
      { TApp (v, args) }
  | v = CAPITAL_IDENT
      { Construct (v, []) }
  | v = CAPITAL_IDENT LPAREN args = separated_list(COMMA, term) RPAREN
      { Construct (v, args) }
  | LBRACKET items = separated_list(SEMI, term) RBRACKET
      { List.fold_right (fun v t -> BinOp (TCons, v, t)) items (Const Nil) }
  (* intended: function body spans maximally *)
  (* todo: remove the parens around function body *)
  | FUN LPAREN args = separated_list(COMMA, LOWERCASE_IDENT) RPAREN MINUSGREATER LPAREN body=staged_spec RPAREN
      { TLambda ("", args, Some body, None) }
;

pi:
  | TRUE
      { True }
  | FALSE
      { False }
  | t1 = term op = bin_rel_op t2 = term
      { Atomic (op, t1, t2) }
  // | a = pure_formula_term SUBSUMES b = pure_formula_term { Subsumption (a, b) }
  | p1 = pi CONJUNCTION p2 = pi
      { And (p1, p2) }
  // these cause shift-reduce conflicts, are not used, and are not in the symbolic heap fragment
//   | p1 = pi DISJUNCTION p2 = pi
//       { Or (p1, p2) }
  // | pure_formula IMPLICATION pure_formula { Imply ($1, $3) }
  | TILDE p = pi
      { Not p }
//   | v = LOWERCASE_IDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, pure_formula_term), RPAREN) { Predicate (v, args) }
  | p = delimited(LPAREN, pi, RPAREN)
      { p }
;

kappa:
  | EMP
      { EmptyHeap }
  | v = LOWERCASE_IDENT MINUSGREATER t = term
      { PointsTo (v, t) }
  | k1 = kappa STAR k2 = kappa
      { SepConj (k1, k2) }
  | k = delimited(LPAREN, kappa, RPAREN)
      { k }
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

fn:
  | v = LOWERCASE_IDENT LPAREN args = separated_list(COMMA, term) RPAREN
    { (v, args) }
;

staged_spec:
  | EXISTS vs = LOWERCASE_IDENT* DOT s = staged_spec
      { List.fold_right (fun v t -> Exists (v, t)) vs s }
  | FORALL vs = LOWERCASE_IDENT* DOT s = staged_spec
      { List.fold_right (fun v t -> ForAll (v, t)) vs s }
  | s1 = staged_spec DISJUNCTION s2 = staged_spec
      { Disjunction (s1, s2) }
  | REQUIRES s = state
      { let (p, k) = s in Require (p, k) }
  | ENSURES s = state
      { let (p, k) = s in NormalReturn (p, k) }
  | va = fn
      { let (v, args) = va in HigherOrder (v, args) }
  | SHIFT LPAREN v = LOWERCASE_IDENT DOT s = staged_spec RPAREN
      { (* TODO: shiftc *)
        let x = Variables.fresh_variable ~v:"x" "continuation argument" in
        Shift (true, v, s, x, NormalReturn (Atomic (EQ, Variables.res_var, Var x), EmptyHeap)) }
  | RESET LPAREN s = staged_spec RPAREN
      { let x = Variables.fresh_variable ~v:"x" "continuation argument" in
        Reset (s, x, NormalReturn (Atomic (EQ, Variables.res_var, Var x), EmptyHeap)) }
  | s1 = staged_spec SEMI s2 = staged_spec
      { Sequence (s1, s2) }
  | LET v = LOWERCASE_IDENT EQUAL s1 = staged_spec IN s2 = staged_spec
      { Bind (v, s1, s2) }
  | LPAREN s = staged_spec RPAREN
      { s }
;

lemma:
  | name_params=fn EQUAL lhs=staged_spec LONGARROW rhs=staged_spec
    { let (f, params) = name_params in
      let params =
        List.map (function Var s -> s | _ -> failwith "invalid lemma") params
      in
      { l_name = f;
        l_params = params;
        l_left = lhs;
        l_right = rhs }
    }
;

parse_pi:
  | p = pi EOF
      { p }

parse_kappa:
  | k = kappa EOF
      { k }

parse_staged_spec:
  | s = staged_spec EOF
      { s }

parse_term:
  | t = term EOF
      { t }

parse_lemma:
  | t = lemma EOF
      { t }

parse_state:
  | t = state EOF
      { t }
