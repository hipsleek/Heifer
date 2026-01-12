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
  | None -> TSymbol {sym_name = x}
  | Some v -> TVar v
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
%nonassoc REQUIRES ENSURES
%nonassoc FORALL EXISTS // lower than ;
%right DISJUNCTION
%right SEMI

// prop
%nonassoc EQUAL
%nonassoc GREATER
%nonassoc LESS
%right EQUALGREATER
%left CONJUNCTION

// hprop
%right STAR

// term
%left PLUS //MINUS
%left STARDOT // multiplication
%right COLONCOLON
// %nonassoc TILDE
// %nonassoc DOT
// %nonassoc IN

%start parse_prop
%type <prop> parse_prop
%start parse_hprop
%type <hprop> parse_hprop
%start parse_staged_spec
%type <staged_spec> parse_staged_spec
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

term:
  | LPAREN RPAREN
  // | c = const
      { TUnit }
  | n = INT
      { TInt n }
  | TRUE
      { TTrue }
  | FALSE
      { TFalse }

  | x=LOWERCASE_IDENT
      { resolve_identifier x }

//   | TILDE t = term
//       { TNot t }
  // | t1 = term op = bin_rel_op t2 = term
//       { Rel (op, t1, t2) }

  | t1=term op=bin_op t2=term
      { TBinop (op, t1, t2) }

  | v=LOWERCASE_IDENT DOLLAR LPAREN args=separated_list(COMMA, term) RPAREN
      { TApp (v, args) }

//   | v = CAPITAL_IDENT
//       { Construct (v, []) }
//   | v = CAPITAL_IDENT LPAREN args = separated_list(COMMA, term) RPAREN
//       { Construct (v, args) }

  // | f=LOWERCASE_IDENT items=delimited(LPAREN, separated_nonempty_list(COMMA, term), RPAREN)
  //     { TApp (f, items) }

  | LBRACKET RBRACKET
      { TNil }
  | items=delimited(LBRACKET, separated_nonempty_list(SEMI, term), RBRACKET)
      { List.fold_right (fun v t -> TBinop (Cons, v, t)) items TNil }
  | items=delimited(LPAREN, separated_nonempty_list(COMMA, term), RPAREN)
    // delimited(LPAREN, separated_nonempty_list(COMMA, term), RPAREN)
// //   | v = LOWERCASE_IDENT args=
      { TTuple items }
      // List.fold_right (fun v t -> BinOp (TCons, v, t)) items (Const Nil)
//   (* intended: function body spans maximally *)
//   (* todo: remove the parens around function body *)

  | LPAREN FUN xs=binders MINUSGREATER s=staged_spec RPAREN
    { let xs = Binders.remove_all xs in
      TFun (unbox (bind_mvar xs (box_staged_spec s))) }
  ;

prop:
  // | TRUE
  //     { PAtom TTrue }
  // | FALSE
  //     { PAtom TFalse }
  // | t1 = term op = bin_op t2 = term
  //     { PAtom (TBinop (op, t1, t2)) }

  | t1=term
    { PAtom t1 }

  | p1 = prop CONJUNCTION p2 = prop
    { PConj (p1, p2) }

  | p1 = prop EQUALGREATER p2 = prop
    { PImplies (p1, p2) }

  | a = staged_spec SUBSUMES b = staged_spec
    { PSubsumes (a, b) }

  | FORALL xs = binders DOT
    p = prop %prec FORALL
      { let xs = Binders.remove_all xs in
        PForall (unbox (bind_mvar xs (box_prop p))) }

//   // these cause shift-reduce conflicts, are not used, and are not in the symbolic heap fragment
// //   | p1 = prop DISJUNCTION p2 = prop
// //       { Or (p1, p2) }
//   // | pure_formula IMPLICATION pure_formula { Imply ($1, $3) }
//   | TILDE p = prop
//       { Not p }
// //   | v = LOWERCASE_IDENT args=delimited(LPAREN, separated_nonempty_list(COMMA, pure_formula_term), RPAREN) { Predicate (v, args) }
//   | p = delimited(LPAREN, prop, RPAREN)
//       { p }
;

hprop:
  | EMP
      { HEmp }
  | l=term MINUSGREATER v=term
      { HPointsTo (l, v) }
  | k1 = hprop STAR k2 = hprop
      { HSepConj (k1, k2) }
  | p = prop %prec CONJUNCTION // this should be the highest level below star
  { HPure p }
  // | k = delimited(LPAREN, hprop, RPAREN)
  //     { k }
;

// fn:
//   | v = LOWERCASE_IDENT LPAREN args = separated_list(COMMA, term) RPAREN
//     { (v, args) }
// ;

staged_spec:
  | s1 = staged_spec DISJUNCTION s2 = staged_spec
      { Disjunct (s1, s2) }
  | RETURN t = term
      { Return t }

  | REQUIRES h = hprop
      { Requires h }
  | ENSURES h = hprop
      { Ensures h }

  | f=term arg=term+
    { Apply (f, arg) }

  // | va = fn
  //     { let (v, args) = va in HigherOrder (v, args) }
  // | SHIFT LPAREN v = LOWERCASE_IDENT DOT s = staged_spec RPAREN
  //     { (* TODO: shiftc *)
  //       let x = Variables.fresh_variable ~v:"x" "continuation argument" in
  //       Shift (true, v, s, x, NormalReturn (Atomic (EQ, Variables.res_var, Var x), EmptyHeap)) }

  | RESET LPAREN s=staged_spec RPAREN
      { Reset s }
  | s1=staged_spec SEMI s2=staged_spec
      { Sequence (s1, s2) }

//   | LET x=LOWERCASE_IDENT EQUAL s1=staged_spec IN s2=staged_spec
  | s1=staged_spec SEMI x=binder DOT
    s2=staged_spec %prec SEMI
      {
        let x = Binders.remove x in
        (* TODO quadratic, possibly return a box from the rules *)
        Bind (s1, unbox (bind_var x (box_staged_spec s2))) }

  | FORALL xs = binders DOT
    s = staged_spec %prec FORALL
      { let xs = Binders.remove_all xs in
        Forall (unbox (bind_mvar xs (box_staged_spec s))) }

  | EXISTS xs = binders DOT
    s = staged_spec %prec EXISTS
      { let xs = Binders.remove_all xs in
        Exists (unbox (bind_mvar xs (box_staged_spec s))) }

  | LPAREN s = staged_spec RPAREN
      { s }
;

def:
  | xs = binders EQUAL s = staged_spec
    { let xs = Binders.remove_all xs in
      unbox (bind_mvar xs (box_staged_spec s)) }

symbol:
  | x = LOWERCASE_IDENT
    { {sym_name = x} }

binders:
  | xs=LOWERCASE_IDENT*
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
//   | name_params=fn EQUAL lhs=staged_spec LONGARROW rhs=staged_spec
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

parse_prop:
  | p = prop EOF
      { Binders.reset_state (); p }

parse_hprop:
  | k = hprop EOF
      { Binders.reset_state (); k }

parse_staged_spec:
  | s = staged_spec EOF
      { Binders.reset_state (); s }

parse_term:
  | t = term EOF
      { t }

// at the moment, the only declaration we may have is function declaration.
parse_decl:
  | sym = symbol def = def EOF
    { Dfun (sym, def) }

// parse_lemma:
//   | t = lemma EOF
//       { t }
