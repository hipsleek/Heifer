open Why3
open Core.Syntax
open Ptree
open Ptree_helpers

let rec term_to_whyml t =
  match t with
  | TUnit -> term (Ttuple [])
  | TTrue -> term Ttrue
  | TFalse -> term Tfalse
  | TNil -> tapp (qualid ["[]"]) []
  | TInt i -> tconst i
  | TBinop (Lt, a, b) ->
    tapp (qualid [Ident.op_infix "<"]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Le, a, b) ->
    tapp (qualid [Ident.op_infix "<="]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Gt, a, b) ->
    tapp (qualid [Ident.op_infix ">"]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Ge, a, b) ->
    tapp (qualid [Ident.op_infix ">="]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Neq, a, b) ->
    tapp (qualid [Ident.op_infix "!="]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Eq, a, b) ->
    tapp (qualid [Ident.op_infix "="]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Times, a, b) ->
    tapp (qualid ["Int"; Ident.op_infix "*"]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Plus, a, b) ->
    tapp (qualid ["Int"; Ident.op_infix "+"]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Cons, h, t) ->
    tapp (qualid ["::"]) [term_to_whyml h; term_to_whyml t]
  | TUnop (Not, a) -> tapp (qualid ["Bool"; "notb"]) [term_to_whyml a]
  | TVar x -> tvar (qualid [Bindlib.name_of x])
  | TSymbol _ -> failwith "symbol"
  | TFun _ -> failwith "todo fun"
  | TTuple _ -> failwith "todo tuple"
  | TUnop (Neg, _) -> failwith "todo unop"

and prop_to_whyml p =
  match p with
  (* | True -> term Ttrue
  | False -> term Tfalse
  | Atomic (EQ, a, b) ->
    tapp
      (qualid [Ident.op_infix "="])
      [term_to_whyml a; term_to_whyml b]
  | Atomic (op, a, b) -> term_to_whyml (Syntax.rel op a b)
  | And (a, b) -> *)
  | PAtom t -> term_to_whyml t
  | PConj (a, b) ->
    term (Tbinop (prop_to_whyml a, Dterm.DTand, prop_to_whyml b))
  (* | Or (a, b) ->
    term (Tbinop (pi_to_whyml a, Dterm.DTor, pi_to_whyml b))
  | Not a -> term (Tnot (pi_to_whyml a)) *)
  | PImplies (a, b) ->
    term (Tbinop (prop_to_whyml a, Dterm.DTimplies, prop_to_whyml b))
  | PSubsumes (_, _) -> term Ttrue
