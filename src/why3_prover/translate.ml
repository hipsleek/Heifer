open Why3
open Core.Syntax
open Ptree
open Ptree_helpers

let tstr s = term (Tconst (Constant.ConstStr s))
let empty_map = tvar (qualid ["Map"; "empty"])

let rec term_to_whyml_aux ctxt t =
  match t with
  | Unit -> term (Ttuple [])
  (* | True -> tapp (qualid ["TBool"]) [term Ttrue]
  | False -> tapp (qualid ["TBool"]) [term Tfalse] *)
  | Nil -> tapp (qualid ["TNil"]) []
  | Int i -> tapp (qualid ["TInt"]) [tconst i]
  (* | Binop (Lt, a, b) ->
    tapp
      (qualid [Ident.op_infix "<"])
      [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Le, a, b) ->
    tapp
      (qualid [Ident.op_infix "<="])
      [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Gt, a, b) ->
    tapp
      (qualid [Ident.op_infix ">"])
      [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Ge, a, b) ->
    tapp
      (qualid [Ident.op_infix ">="])
      [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Neq, a, b) ->
    tapp
      (qualid [Ident.op_infix "!="])
      [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Eq, a, b) ->
    (* tapp (qualid [Ident.op_infix "="]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b] *)
    tapp (qualid ["eq"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b] *)
  | Binop (Times, a, b) ->
      tapp
        (qualid ["Int"; Ident.op_infix "*"])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Plus, a, b) ->
      (* tapp (qualid ["Int"; Ident.op_infix "+"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b] *)
      tapp (qualid ["plus"])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Cons, h, t) ->
      tapp (qualid ["::"]) [term_to_whyml_aux ctxt h; term_to_whyml_aux ctxt t]
  | Unop (Not, a) -> tapp (qualid ["Bool"; "notb"]) [term_to_whyml_aux ctxt a]
  | Var x ->
      (* tvar (qualid [Bindlib.name_of x]) *)
      tapp (qualid ["Var"]) [tstr (Bindlib.name_of x)]
  (* | Apply (f, args) -> tapp (qualid [f]) (List.map term_to_whyml_aux ctxt args) *)
  | Apply (Symbol { sym_name = f }, args) ->
      tapp (qualid [f]) (List.map (term_to_whyml_aux ctxt) args)
  | Apply (_f, _args) -> failwith "apply"
  | Symbol _ -> failwith "symbol"
  | Fun _ -> failwith "todo fun"
  | Tuple _ -> failwith "todo tuple"
  | Unop (Neg, _) -> failwith "todo unop"
  | Emp | PointsTo _ | SepConj _ ->
      failwith "separation logic cannot be translated"
  | Subsumes _ -> failwith "subsumptions not handled at this level"
  | Requires _ | Ensures _ | Sequence (_, _) | Shift _ | Reset _ | Bind (_, _)
    ->
      failwith "staged logic not handled at this level"
  (* | Conj (_, _)
  | Disj (_, _)
  | Implies (_, _)
  | Forall _ | Exists _ *)
  | Forall b ->
      let xs, b, ctxt = Bindlib.unmbind_in ctxt b in
      let xs = Array.to_list xs in
      List.fold_right
        (fun c t -> tapp (qualid ["PForall"]) [tstr (Bindlib.name_of c); t])
        xs (term_to_whyml_aux ctxt b)
  | Exists b ->
      let xs, b, ctxt = Bindlib.unmbind_in ctxt b in
      let xs = Array.to_list xs in
      List.fold_right
        (fun c t -> tapp (qualid ["PExists"]) [tstr (Bindlib.name_of c); t])
        xs (term_to_whyml_aux ctxt b)
      (* [tconst i] *)
      (* tapp (qualid ["eq"]) *)
      (* [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b] *)
      (* failwith "cannot translate forall" *)
  | True -> tapp (qualid ["PTrue"]) []
  | False -> tapp (qualid ["PFalse"]) []
  | Binop (Eq, a, b) ->
      tapp (qualid ["PEq"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Gt, a, b) ->
      tapp (qualid ["PGt"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Lt, a, b) ->
      tapp (qualid ["PLt"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Le, a, b) ->
      tapp (qualid ["PLe"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Ge, a, b) ->
      tapp (qualid ["PGe"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Binop (Neq, a, b) ->
      tapp (qualid ["PNeq"])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
      (* | PAtom _ ->
    Format.printf "%a@." Core.Pretty.pp_prop p;
    failwith "unimplemented" *)
      (* term_to_whyml_aux ctxt t *)
      (* tapp (qualid ["interp_term"]) [empty_map; term_to_whyml_aux ctxt t] *)
      (* tapp (qualid ["PAtom"]) [term_to_whyml_aux ctxt t] *)
  | Conj (a, b) ->
      tapp (qualid ["PAnd"])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  | Disj (a, b) ->
      tapp (qualid ["POr"]) [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
  (* term
      (Tbinop (term_to_whyml_aux ctxt a, Dterm.DTand, term_to_whyml_aux ctxt b)) *)
  (* | Or (a, b) ->
    term (Tbinop (pi_to_whyml a, Dterm.DTor, pi_to_whyml b))
  | Not a -> term (Tnot (pi_to_whyml a)) *)
  | Implies (a, b) ->
      tapp (qualid ["PImplies"])
        [term_to_whyml_aux ctxt a; term_to_whyml_aux ctxt b]
(* term (Tbinop (, Dterm.DTimplies, )) *)
(* term (Tbinop (term_to_whyml_aux a, Dterm.DTimplies, term_to_whyml_aux b)) *)

(* let rec term_to_whyml_aux ctxt p = *)
(* match p with *)

(* | PSubsumes _ -> term Ttrue *)

let term_to_whyml p =
  let p1 = term_to_whyml_aux Bindlib.(free_vars (box_prop p)) p in
  tapp (qualid ["interp"]) [empty_map; p1]
