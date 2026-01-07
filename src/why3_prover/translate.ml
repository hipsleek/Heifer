open Why3
open Core.Syntax
open Ptree
open Ptree_helpers

let rec term_to_whyml t =
  match t with
  | TUnit -> term (Ttuple [])
  | TTrue -> term Ttrue
  | TFalse -> term Tfalse
  | TNil | TVar _ | TInt _ | TFun _ | TTuple _ | TBinop (_, _, _) | TUnop (_, _)
    ->
    failwith "todo"

(* | Const TTrue -> term Ttrue
  | Const TFalse -> term Tfalse
  | Const (Num i) -> tconst i
  | Var v -> tvar (qualid [v])
  | BinOp (SConcat, a, b) ->
    tapp
      (qualid ["String"; "concat"])
      [term_to_whyml a; term_to_whyml b]
  | BinOp (Plus, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "+"])
      [term_to_whyml a; term_to_whyml b]
  | BinOp (Minus, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "-"])
      [term_to_whyml a; term_to_whyml b]
  | BinOp (TTimes, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "*"])
      [term_to_whyml a; term_to_whyml b]
  | Rel (EQ, a, b) ->
    tapp
      (qualid [Ident.op_infix "="])
      [term_to_whyml a; term_to_whyml b]
  | Rel (GT, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix ">"])
      [term_to_whyml a; term_to_whyml b]
  | Rel (GTEQ, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix ">="])
      [term_to_whyml a; term_to_whyml b]
  | Rel (LT, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "<"])
      [term_to_whyml a; term_to_whyml b]
  | Rel (LTEQ, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "<="])
      [term_to_whyml a; term_to_whyml b]
  | BinOp (TAnd, a, b) ->
    tapp (qualid ["Bool"; "andb"]) [term_to_whyml a; term_to_whyml b]
  | BinOp (TOr, a, b) ->
    tapp (qualid ["Bool"; "orb"]) [term_to_whyml a; term_to_whyml b]
  | TNot a -> tapp (qualid ["Bool"; "notb"]) [term_to_whyml a]
  | TApp (f, args) -> tapp (qualid [f]) (List.map (term_to_whyml) args)
  | Const Nil -> tapp (qualid ["[]"]) []
  | BinOp (TCons, h, t) ->
    tapp (qualid ["::"]) [term_to_whyml h; term_to_whyml t]
  | TLambda (_name, _, _sp, Some _) | TLambda (_name, _, _sp, None) ->
    (* if there is no body, generate something that only respects alpha equivalence *)
    (* this probably doesn't always work *)
    (* tconst (Subst.hash_lambda t) *)
    failwith "lambda"
  (* failwith "no body" *)
  (* disabled temporarily *)
  (* | TLambda (_name, params, _sp, Some body) ->
     let params, _ret = unsnoc params in
     let binders = vars_to_params tenv params in
     term (Tquant (Dterm.DTlambda, binders, [], core_lang_to_whyml tenv body)) *)
  | Construct (name, []) ->
    term (Tident (qualid [name]))
  | Construct (name, args) ->
      tapp (qualid [name]) (List.map term_to_whyml args)
  | TTuple _ | BinOp (TPower, _, _) | BinOp (TDiv, _, _) | Const (TStr _) *)

(* -> *)
(* failwith "nyi" *)

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
  | PImplies (_, _)
  (* | Predicate (_, _) -> failwith "nyi" *)
  | PSubsumes (_, _) ->
    (* term Ttrue *)
    failwith "todo"
