open Hipcore
open Hiptypes

(** goes down the given spec trying to match the lemma's left side, and rewriting on match. may fail *)
(** TODO: rewrite this *)
(** What we need here is some kind of unification between the LHS of a lemma and the spec *)
(** How to do the unification tho? *)
let todo () = failwith "todo"

(* we need a mapping from variable -> term *)
(* in the enviroment, variable can either be *)

(* We can run in two steps: unify and then check for alpha-equivalence? *)
type unification_val =
  | Subst_none
  | Subst_term of term
  | Subst_string of string

type unification_env = unification_val SMap.t

exception Unification_failure

(* let unify_lem_lhs_args params la a =
  (* debug ~at:4 ~title:"unify_lem_lhs_args" "%s\n%s\n%s"
    (string_of_list Fun.id params)
    (string_of_list string_of_term la)
    (string_of_list string_of_term a); *)
  let exception Unification_failure in
  try
    Some
      (List.map2 pair la a |> List.fold_left
         (fun t (la, a) ->
           let is_param =
             match la with Var v when List.mem v params -> true | _ -> false
           in
           match (is_param, la) with
           | true, Var la -> (la, a) :: t
           | false, _ when la = a -> t
           | false, _ -> raise_notrace Unification_failure
           | _, _ -> failwith "invalid state")
         [])
  with Unification_failure -> None *)

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
  | TApp (s1, t1s), TApp (s2, t2s) ->
      ignore (s1, t1s, s2, t2s);
      todo ()
  | TLambda _, TLambda _ ->
      (* difficult *)
      todo ()
  | TList t1s, TList t2s
  | TTupple t1s, TTupple t2s ->
      unify_term_list t1s t2s e
  | Var _, _ ->
      todo ()
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
      (* Assume that we cannot quantify over predicate name *)
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
      (* unify the two string s1 and s2 if possible *)
      ignore (s1, s2);
      unify_term t1 t2 e
  | SepConj (k11, k12), SepConj (k21, k22) ->
      unify_kappa k12 k22 (unify_kappa k11 k21 e)
  | _, _ ->
      raise Unification_failure

(* all unification functions must have an enviroment *)
(* the idea behind this is that we traverse two trees together,
   and then try to unify *)
let rec unify_stagedSpec (ssp1 : stagedSpec) (ssp2 : stagedSpec) (e : unification_env) : unification_env =
  match ssp1, ssp2 with
  | Exists _, Exists _ ->
      todo ()
  | Require (p1, k1), Require (p2, k2)
  | NormalReturn (p1, k1), NormalReturn (p2, k2) ->
      unify_kappa k1 k2 (unify_pi p1 p2 e)
  | HigherOrder _, HigherOrder _
  | Shift _, Shift _
  | Reset _, Reset _ ->
      todo ()
  | RaisingEff _, RaisingEff _ ->
      failwith "unify_stagedSpec: matching RaisingEff, but not supported"
  | TryCatch _, TryCatch _ ->
      failwith "unify_stagedSpec: matching TryCatch, but not supported"
  | _ -> todo ()

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

(*
let apply_lemma : lemma -> spec -> spec option =
  fun lem sp ->
    let@ _ =
      Debug.span (fun r ->
        debug ~at:3
          ~title:"apply_lemma"
          "lemma: %s\nspec: %s\nres: %s"

          (* observation: the old lemma is to be applied on a single stage *)
          (* which is different from this lemma, which is to be applied on the entire spec *)
          (string_of_lemma lem)
          (string_of_spec sp)
          (string_of_result (string_of_option string_of_spec) r))
    in
    let lem = rename_exists_lemma lem in
    let rec loop ok acc sp =
      match sp with
      | [] -> (Acc.to_list acc, ok)
      | st :: sp1 ->
          let lf, largs = lem.l_left in
          begin match st with
          | TryCatch _ -> failwith "unimplemented"
          | Reset _ -> failwith "unimplemented"
          | Shift _ -> failwith "unimplemented"
          | HigherOrder (p, h, (f, args), r)
              when (not ok) (* only apply once *) && f = lf ->
              begin match unify_lem_lhs_args lem.l_params largs (args @ [r]) with
              | Some bs ->
                  let inst_lem_rhs = List.map (instantiateStages bs) lem.l_right in
                  let extra_ret_equality =
             (* TODO *)
                  try
                    let rhs_ret = Forward_rules.retrieve_return_value inst_lem_rhs in
                    Atomic (EQ, r, rhs_ret)
                  with _ ->
                    True
                  in
                  loop true (Acc.add_all
                      (NormalReturn (And (p, extra_ret_equality), h) :: inst_lem_rhs) acc) sp1
              | None ->
                  loop ok (Acc.add st acc) sp1)
       | HigherOrder _
       | NormalReturn _
       | Exists _

       (* observation: the old lemma is to be applied on a single stage *)
       (* which is different from this lemma, which is to be applied on the entire spec *)
       | Require (_, _)
       | RaisingEff _ ->
          loop ok (Acc.add st acc) sp1
   in
   let r, ok = loop false Acc.empty sp in
   if ok then Some r else None

(* literally apply one lemma, we scan the list of lemmas and apply the first one possible *)
let apply_one_lemma : lemma list -> spec -> spec * lemma option =
  fun lems sp ->
    List.fold_left
      (fun (sp, app) l ->
        match app with
        | Some _ -> (sp, app)
        | None ->
            let sp1 = apply_lemma l sp in
            match sp1 with None -> (sp, app) | Some sp1 -> (sp1, Some l))
      (sp, None) lems
*)