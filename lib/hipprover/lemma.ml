open Hipcore
open Hiptypes

let todo () = failwith "todo"

(** A mapping from variables -> variables/terms *)
type unification_val =
  | U_none
  | U_term of term
  | U_string of string
  | U_alpha of string (* for alpha-equivalence *)

type unification_env = unification_val SMap.t

exception Unification_failure

let unify_string (s1 : string) (s2 : string) (e : unification_env) : unification_env =
  (* if s1 is not present, s1 is not a bound variable. Error! *)
  (* if s1 is present, then it is mapped to a unification_val *)
  (* now consider the unification_val *)
    (* if it is a none, we add a new binding *)
    (* if it is a string, we check for equality in the content *)
    (* if it is a term, fail *)
  let uval = try SMap.find s1 e with Not_found -> raise Unification_failure in
  match uval with
  | U_none ->
      SMap.add s1 (U_string s2) e
  | U_string s2'
  | U_alpha s2' when s2 = s2' ->
      e
  | _ ->
      raise Unification_failure

let unify_var (s : string) (t : term) (e : unification_env) : unification_env =
  let uval = try SMap.find s e with Not_found -> raise Unification_failure in
  match uval with
  | U_none ->
      SMap.add s (U_term t) e
  | U_term t' when t = t' ->
      (* Do we need to check for alpha-equivalence? *)
      e
  | U_alpha s_alpha ->
      begin match t with
      | Var s' when s_alpha = s' -> e
      | _ -> raise Unification_failure
      end
  | _ ->
      raise Unification_failure

(** "Unify" two bounded variables introduced by exists/shift/lambda.
    This "unification" is to support checking for alpha-equivalence.
    The alpha-"unification" will be removed during substituition.
  *)
let unify_alpha (s1 : string) (s2 : string) (e : unification_env) : unification_env =
  (* if s1 exists already, we override it *)
  SMap.add s1 (U_alpha s2) e

let ununify_alpha (s1 : string) (s2 : string) (e : unification_env) : unification_env =
  let uval =
    try
      SMap.find s1 e
    with Not_found ->
      failwith "ununify_alpha: binding not found"
  in
  match uval with
  | U_alpha s2' when s2 = s2' ->
      SMap.remove s1 e
  | _ ->
      failwith "ununify_alpha: unexpected binding"

(** unification of two terms. We note that Var can be
    unified with any term in the RHS. We assume that the RHS
    term has no free variable.
  *)
let rec unify_term (t1 : term) (t2 : term)  (e : unification_env) : unification_env =
  match t1, t2 with
  | UNIT, UNIT
  | TTrue, TTrue
  | TFalse, TFalse
  | Nil, Nil ->
      e
  | Num n1, Num n2 when n1 = n2 ->
      e
  | TStr s1, TStr s2 when s1 = s2 ->
      e
  | Plus (t11, t12), Plus (t21, t22)
  | Minus (t11, t12), Minus (t21, t22)
  | TTimes (t11, t12), TTimes (t21, t22)
  | TDiv (t11, t12), TDiv (t21, t22)
  | TPower (t11, t12), TPower (t21, t22)
  | SConcat (t11, t12), SConcat (t21, t22)
  | TAnd (t11, t12), TAnd (t21, t22)
  | TOr (t11, t12), TOr (t21, t22)
  | TCons (t11, t12), TCons (t21, t22) ->
      unify_term t12 t22 (unify_term t11 t21 e)
  | Rel (op1, t11, t12), Rel (op2, t21, t22) when op1 = op2 ->
      unify_term t12 t22 (unify_term t11 t21 e)
  | TNot t1', TNot t2' ->
      unify_term t1' t2' e
  | TApp (s1, t1s), TApp (s2, t2s) when s1 = s2 ->
      (* we cannot quantify over function name *)
      unify_term_list t1s t2s e
  | TLambda _, TLambda _ ->
      (* difficult *)
      failwith "unify_term: matching TLambda, but not supported"
  | TList t1s, TList t2s
  | TTupple t1s, TTupple t2s ->
      unify_term_list t1s t2s e
  | Var s, _ ->
      Debug.debug ~at:2 ~title:"try unify var" "%s %s\n" s (Pretty.string_of_term t2);
      unify_var s t2 e
  | _, _ ->
      raise Unification_failure

and unify_term_list (t1s : term list) (t2s : term list) (e : unification_env) : unification_env =
  try
    List.fold_left2 (fun e' t1 t2 -> unify_term t1 t2 e') e t1s t2s
  with Invalid_argument _ -> (* The two lists have different length *)
    raise Unification_failure

let rec unify_pi (p1 : pi) (p2 : pi) (e : unification_env) : unification_env =
  match p1, p2 with
  | True, True
  | False, False ->
      e
  | Atomic (op1, t11, t12), Atomic (op2, t21, t22) when op1 = op2 ->
      unify_term t12 t22 (unify_term t11 t21 e)
  | And (p11, p12), And (p21, p22)
  | Or (p11, p12), Or (p21, p22)
  | Imply (p11, p12), Imply (p21, p22) ->
      unify_pi p12 p22 (unify_pi p11 p21 e)
  | Not p1', Not p2' ->
      unify_pi p1' p2' e
  | Predicate (s1, t1s), Predicate (s2, t2s) when s1 = s2 ->
      (* we cannot quantify over predicate name *)
      unify_term_list t1s t2s e
  | Subsumption (t11, t12), Subsumption (t21, t22) ->
      unify_term t12 t22 (unify_term t11 t21 e)
  | _, _ ->
      raise Unification_failure

let rec unify_kappa (k1 : kappa) (k2 : kappa) (e : unification_env) : unification_env =
  match k1, k2 with
  | EmptyHeap, EmptyHeap ->
      e
  | PointsTo (s1, t1), PointsTo (s2, t2) ->
      unify_term t1 t2 (unify_string s1 s2 e)
  | SepConj (k11, k12), SepConj (k21, k22) ->
      unify_kappa k12 k22 (unify_kappa k11 k21 e)
  | _, _ ->
      raise Unification_failure

(* all unification functions must have an enviroment *)
(* the idea behind this is that we traverse two trees together,
   and then try to unify *)
let rec unify_stagedSpec (ssp1 : stagedSpec) (ssp2 : stagedSpec) (e : unification_env) : unification_env =
  match ssp1, ssp2 with
  | Exists s1s, Exists s2s ->
      List.fold_left2 (fun e' s1 s2 -> unify_alpha s1 s2 e') e s1s s2s
  | Require (p1, k1), Require (p2, k2)
  | NormalReturn (p1, k1), NormalReturn (p2, k2) ->
      unify_kappa k1 k2 (unify_pi p1 p2 e)
  | HigherOrder ((f1, args1), t1), HigherOrder ((f2, args2), t2) when f1 = f2 ->
      (* failwith "unify_stagedSpec: matching HigherOrder, but not supported" *)
      Debug.debug ~at:2 ~title:"try unify higher-order" "%s, %s\n" f1 f2;
      let e = List.fold_left2 (fun e' arg1 arg2 -> unify_term arg1 arg2 e') e args1 args2 in
      unify_term t1 t2 e
  | Shift (b1, k1, dsp1, t1), Shift (b2, k2, dsp2, t2) when b1 = b2 ->
      (* k1 and k2 are now alpha-equivalence *)
      (* k1 and k2 are only bounded when we are traversing the
         body of shift *)
      let e = unify_alpha k1 k2 e in
      let e = unify_disj_spec dsp1 dsp2 e in
      let e = ununify_alpha k1 k2 e in
      let e = unify_term t1 t2 e in
      e
  | Reset (dsp1, t1), Reset (dsp2, t2) ->
      unify_term t1 t2 (unify_disj_spec dsp1 dsp2 e)
  | RaisingEff _, RaisingEff _ ->
      failwith "unify_stagedSpec: matching RaisingEff, but not supported"
  | TryCatch _, TryCatch _ ->
      failwith "unify_stagedSpec: matching TryCatch, but not supported"
  | _ ->
      raise Unification_failure

and unify_spec (sp1 : spec) (sp2 : spec) (e : unification_env) : unification_env =
  try
    List.fold_left2 (fun e' ssp1 ssp2 -> unify_stagedSpec ssp1 ssp2 e') e sp1 sp2
  with Invalid_argument _ ->
    raise Unification_failure

and unify_disj_spec (dsp1 : disj_spec) (dsp2 : disj_spec) (e : unification_env) : unification_env =
  try
    List.fold_left2 (fun e' sp1 sp2 -> unify_spec sp1 sp2 e') e dsp1 dsp2
  with Invalid_argument _ ->
    raise Unification_failure

(* for the substitution to the RHS, can we use subst.ml? *)
(* Seems like we can use the subst visitor *)

type new_lemma = {
  l_name : string;
  l_params : string list;
  l_left : spec;
  l_right : spec;
}

type new_lemma_1 = {
  l1_name : string;
  l1_params : string list;
  l1_left : stagedSpec;
  l1_right : spec;
}

(* however, we have another version, in which we only apply one a single stage, but we do unification *)
(* on that stage *)

(* l_left is a spec with some generalized variable *)
(* what we need to do is to traverse the lhs and then do unification *)

(* observation: the old lemma is to be applied on a single stage *)
(* which is different from this lemma, which is to be applied on the entire spec *)

(* in any case, after the unification, we will instantiate the spec with the bindings and then *)
(* add everything into an accumulator *)

let create_initial_unification_env (params : string list) =
  List.fold_left (fun acc param -> SMap.add param U_none acc) SMap.empty params

let convert_to_bindings (e : unification_env) =
  let fm (v, u) =
    match u with
    | U_none -> failwith "convert_to_bindings: ununified variable"
    | U_string s -> Some (v, Var s)
    | U_term t -> Some (v, t)
    | U_alpha _ -> None
  in
  List.filter_map fm (SMap.bindings e)
