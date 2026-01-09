open Why3
open Core.Syntax
open Ptree
open Ptree_helpers

let tstr s = term (Tconst (Constant.ConstStr s))
let empty_map = tvar (qualid ["Map"; "empty"])

let rec term_to_whyml t =
  match t with
  | TUnit -> term (Ttuple [])
  | TTrue -> tapp (qualid ["TBool"]) [term Ttrue]
  | TFalse -> tapp (qualid ["TBool"]) [term Tfalse]
  | TNil -> tapp (qualid ["[]"]) []
  | TInt i -> tapp (qualid ["TInt"]) [tconst i]
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
    (* tapp (qualid [Ident.op_infix "="]) [term_to_whyml a; term_to_whyml b] *)
    tapp (qualid ["eq"]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Times, a, b) ->
    tapp (qualid ["Int"; Ident.op_infix "*"]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Plus, a, b) ->
    (* tapp (qualid ["Int"; Ident.op_infix "+"]) [term_to_whyml a; term_to_whyml b] *)
    tapp (qualid ["plus"]) [term_to_whyml a; term_to_whyml b]
  | TBinop (Cons, h, t) ->
    tapp (qualid ["::"]) [term_to_whyml h; term_to_whyml t]
  | TUnop (Not, a) -> tapp (qualid ["Bool"; "notb"]) [term_to_whyml a]
  | TVar x ->
    (* tvar (qualid [Bindlib.name_of x]) *)
    tapp (qualid ["Var"]) [tstr (Bindlib.name_of x)]
  | TApp (f, args) -> tapp (qualid [f]) (List.map term_to_whyml args)
  | TSymbol _ -> failwith "symbol"
  | TFun _ -> failwith "todo fun"
  | TTuple _ -> failwith "todo tuple"
  | TUnop (Neg, _) -> failwith "todo unop"

let rec prop_to_whyml_aux ctxt p =
  match p with
  (* | True -> term Ttrue
  | False -> term Tfalse
  | Atomic (EQ, a, b) ->
    tapp
      (qualid [Ident.op_infix "="])
      [term_to_whyml a; term_to_whyml b]
  | Atomic (op, a, b) -> term_to_whyml (Syntax.rel op a b)
  | And (a, b) -> *)
  | PForall b ->
    let xs, b, ctxt = Bindlib.unmbind_in ctxt b in
    let xs = Array.to_list xs in
    List.fold_right
      (fun c t -> tapp (qualid ["PForall"]) [tstr (Bindlib.name_of c); t])
      xs (prop_to_whyml_aux ctxt b)
    (* [tconst i] *)
    (* tapp (qualid ["eq"]) *)
    (* [term_to_whyml a; term_to_whyml b] *)
    (* failwith "cannot translate forall" *)
  | PAtom TTrue -> tapp (qualid ["PTrue"]) []
  | PAtom TFalse -> tapp (qualid ["PFalse"]) []
  | PAtom (TBinop (Eq, a, b)) ->
    tapp (qualid ["PEq"]) [term_to_whyml a; term_to_whyml b]
  | PAtom _ ->
    Format.printf "%a@." Core.Pretty.pp_prop p;
    failwith "unimplemented"
    (* term_to_whyml t *)
    (* tapp (qualid ["interp_term"]) [empty_map; term_to_whyml t] *)
    (* tapp (qualid ["PAtom"]) [term_to_whyml t] *)
  | PConj (a, b) ->
    term
      (Tbinop (prop_to_whyml_aux ctxt a, Dterm.DTand, prop_to_whyml_aux ctxt b))
  (* | Or (a, b) ->
    term (Tbinop (pi_to_whyml a, Dterm.DTor, pi_to_whyml b))
  | Not a -> term (Tnot (pi_to_whyml a)) *)
  | PImplies (a, b) ->
    tapp (qualid ["PImplies"])
      [prop_to_whyml_aux ctxt a; prop_to_whyml_aux ctxt b]
    (* term (Tbinop (, Dterm.DTimplies, )) *)
    (* term (Tbinop (prop_to_whyml_aux a, Dterm.DTimplies, prop_to_whyml_aux b)) *)
  | PSubsumes _ -> term Ttrue

let prop_to_whyml p =
  let p1 = prop_to_whyml_aux Bindlib.(free_vars (box_prop p)) p in
  tapp (qualid ["interp"]) [empty_map; p1]
