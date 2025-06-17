open Hipcore
open Hiptypes
open Pretty
open Debug
open Normalize

(* type use = Use of string * [ `Left | `Right ] [@unboxed] *)

(* let string_of_use (f, lr) =
  match lr with
  | `Left -> Format.asprintf "%s, L" f
  | `Right -> Format.asprintf "%s, R" f *)

type use = Use of string [@@unboxed]

let string_of_use (Use f) = f

(** proof context *)
type pctx = {
  constants : term list;
  definitions_nonrec : (string * Rewriting.rule) list;
  definitions_rec : (string * Rewriting.rule) list;
  induction_hypotheses : (string * Rewriting.rule) list;
  lemmas : Rewriting.rule list;
  unfolded : use list;
  assumptions : pi list;
}

let string_of_pctx ctx =
  let {
    constants;
    assumptions;
    definitions_nonrec;
    definitions_rec;
    unfolded;
    induction_hypotheses;
    lemmas;
  } =
    ctx
  in
  let open Rewriting in
  Format.asprintf
    "constants:\n\
     %s\n\n\
     induction_hypotheses:\n\
     %s\n\n\
     lemmas:\n\
     %s\n\n\
     assumptions:\n\
     %s\n\n\
     definitions_nonrec:\n\
     %s\n\n\
     definitions_rec:\n\
     %s\n\n\
     unfolded:\n\
     %s"
    (string_of_list string_of_term constants)
    (string_of_list_ind_lines
       (string_of_pair Fun.id string_of_rule)
       induction_hypotheses)
    (string_of_list_ind_lines string_of_rule lemmas)
    (string_of_list_ind_lines string_of_pi assumptions)
    (string_of_list_ind_lines
       (string_of_pair Fun.id string_of_rule)
       definitions_nonrec)
    (string_of_list_ind_lines
       (string_of_pair Fun.id string_of_rule)
       definitions_rec)
    (string_of_list_ind_lines string_of_use unfolded)

let new_pctx () =
  {
    constants = [];
    assumptions = [];
    definitions_nonrec = [];
    definitions_rec = [];
    unfolded = [];
    induction_hypotheses = [];
    lemmas = [];
  }

let has_been_unfolded pctx name _lr =
  pctx.unfolded
  |> List.find_opt
       (* (fun (u, lr1) -> u = name && lr = lr1) *)
       (fun (Use u) -> u = name)
  |> Option.is_some

let pred_to_rule pred =
  let params = pred.p_params |> List.map Rewriting.Rules.Term.uvar in
  let lhs = HigherOrder (pred.p_name, params) in
  let rhs =
    let bs =
      List.map (fun p -> (p, Rewriting.Rules.Term.uvar p)) pred.p_params
    in
    Subst.subst_free_vars bs pred.p_body
  in
  (pred.p_name, Rewriting.Rules.Staged.rule lhs rhs)

let create_pctx cp =
  let definitions_nonrec =
    SMap.values cp.cp_predicates
    |> List.filter (fun p -> not p.p_rec)
    |> List.map pred_to_rule
  in
  let definitions_rec =
    SMap.values cp.cp_predicates
    |> List.filter (fun p -> p.p_rec)
    |> List.map pred_to_rule
  in
  { (new_pctx ()) with definitions_nonrec; definitions_rec }

(* proof state *)
type pstate = pctx * staged_spec * staged_spec

(* prints the proof state like an inference rule *)
(* let string_of_pstate (ctx, left, right) =
  Format.asprintf "%s\n%s\n%s\n⊑\n%s" (string_of_pctx ctx) (String.make 60 '-')
    (string_of_staged_spec left)
    (string_of_staged_spec right) *)

(* this version is more usable for seeing the goal *)
let string_of_pstate =
  let backarrow = "<" ^ String.make 60 '=' in
  fun (ctx, left, right) ->
    Format.asprintf "%s\n⊑\n%s\n%s\n%s"
      (string_of_staged_spec left)
      (string_of_staged_spec right)
      backarrow (string_of_pctx ctx)

(* let pctx_to_supp ctx =
  let open Rewriting in
  let {
    assumptions;
    definitions_nonrec;
    definitions_rec;
    unfolded;
    induction_hypotheses;
    lemmas;
  } =
    ctx
  in
  [
    ("assumptions", string_of_list_lines string_of_pi assumptions);
    ( "induction hypotheses",
      string_of_list_lines
        (string_of_pair Fun.id string_of_rule)
        induction_hypotheses );
    ("lemmas", string_of_list_lines string_of_rule lemmas);
    ( "definitions_nonrec",
      string_of_list_lines
        (string_of_pair Fun.id string_of_rule)
        definitions_nonrec );
    ( "definitions_rec",
      string_of_list_lines
        (string_of_pair Fun.id string_of_rule)
        definitions_rec );
    ( "unfolded",
      string_of_list_lines
        (fun (f, lr) ->
          match lr with
          | `Left -> Format.asprintf "%s, L" f
          | `Right -> Format.asprintf "%s, R" f)
        unfolded );
  ] *)

let pctx_to_supp ?(title = "proof context") ctx = [(title, string_of_pctx ctx)]

let log_proof_state ~title (pctx, f1, f2) =
  let supp = pctx_to_supp pctx in
  debug ~at:4 ~title ~supp "%s\n⊑\n%s" (string_of_staged_spec f1)
    (string_of_staged_spec f2)

let log_proof_state_total ~title (pctx, f1, f2) ps1 =
  let supp, res =
    match ps1 with
    | Value (pctx1, f3, f4) ->
      ( pctx_to_supp ~title:"proof context before" pctx
        @ pctx_to_supp ~title:"proof context after" pctx1,
        Format.asprintf "%s\n⊑\n%s" (string_of_staged_spec f3)
          (string_of_staged_spec f4) )
    | _ -> (pctx_to_supp pctx, string_of_result (fun _ -> "") ps1)
  in
  debug ~at:4 ~title ~supp "%s\n⊑\n%s\n==>\n%s" (string_of_staged_spec f1)
    (string_of_staged_spec f2) res

let check_pure_obligation left right =
  let@ _ =
    span (fun r ->
        debug ~at:4 ~title:"check_pure_obligation" "%s => %s ? %s"
          (string_of_pi left) (string_of_pi right)
          (string_of_result string_of_bool r))
  in
  let open Infer_types in
  let tenv =
    (* handle the environment manually as it's shared between both sides *)
    let env = create_abs_env () in
    let env = infer_types_pi env left in
    let env = infer_types_pi env right in
    env
  in
  let res = Provers.entails_exists (concrete_type_env tenv) left [] right in
  res

(* will be used for remembering predicate? Not sure whether it should be put here *)
let derive_predicate m_name m_params f =
  let new_spec = normalize_spec f in
  let@ _ =
    Debug.span (fun res ->
        debug ~at:2
          ~title:(Format.asprintf "derive predicate %s" m_name)
          "%s\n\n%s"
          (string_of_staged_spec new_spec)
          (string_of_result string_of_pred res))
  in
  let res =
    {
      p_name = m_name;
      p_params = m_params;
      p_body = new_spec;
      p_rec = (find_rec m_name)#visit_staged_spec () new_spec;
    }
  in
  res

let lambda_to_rule m_name m_params f =
  derive_predicate m_name m_params f |> pred_to_rule

(** Tactics combine the state and list monads *)
module Tactic : sig
  type 'a t = pstate -> ('a * pstate) Iter.t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val get : pstate t
  val put : pstate -> unit t
  val fail : 'a t
end = struct
  type 'a t = pstate -> ('a * pstate) Iter.t

  let return x = fun s -> Iter.return (x, s)
  let bind m f = fun s -> Iter.flat_map (fun (x, s') -> f x s') (m s)
  let get = fun s -> Iter.return (s, s)
  let put s = fun _ -> Iter.return ((), s)
  let fail = fun _ -> Iter.empty
  let ( >>= ) = bind
  let ( let* ) = bind
end

type tactic = pstate -> pstate Iter.t

let fail = ()

let or_ f g k =
  let elt = ref false in
  f (fun a ->
      elt := true;
      k a);
  if not !elt then g k

let rec disj_ fs k =
  match fs with
  | [] -> fail
  | f :: fs1 ->
    let elt = ref false in
    f (fun a ->
        elt := true;
        k a);
    if not !elt then disj_ fs1 k

(* a total tactic, which does not fail or backtrack *)
type total = pstate -> pstate

let unfold_recursive_defns pctx f lr =
  let open Rewriting in
  let open Rules.Staged in
  let@ _ =
    span (fun r ->
        debug ~at:4 ~title:"unfold_recursive_defns" "used: %s"
          (string_of_result (fun (_, _, u) -> string_of_list string_of_use u) r))
  in
  let usable_defns =
    pctx.definitions_rec
    |> List.filter (fun (rule_name, _rule) ->
           not (has_been_unfolded pctx rule_name lr))
  in
  let f, used =
    List.fold_right
      (fun (name, rule) (f, used) ->
        let f1 = rewrite_all rule (Staged f) |> of_uterm in
        let u = if f = f1 then [] else [Use name] in
        (f1, u @ used))
      usable_defns (f, [])
  in
  debug ~at:2 ~title:"used rules" "%s" (string_of_list string_of_use used);
  ({ pctx with unfolded = used @ pctx.unfolded }, f, used)

let unfold_nonrecursive_defns defns f =
  let open Rewriting in
  let open Rules.Staged in
  let db = List.map snd defns in
  let f = autorewrite db (Staged f) |> of_uterm in
  f

let unfold_definitions : total =
 fun ps ->
  let@ _ =
    span (fun r -> log_proof_state_total ~title:"unfold_definitions" ps r)
  in
  let pctx, f1, f2 = ps in
  (* unfold nonrecursive *)
  let f1, f2 =
    let@ _ = span (fun _r -> debug ~at:5 ~title:"nonrecursive" "") in
    let f1 = unfold_nonrecursive_defns pctx.definitions_nonrec f1 in
    let f2 = unfold_nonrecursive_defns pctx.definitions_nonrec f2 in
    (f1, f2)
  in
  (* unfold recursive *)
  let pctx, f1, _ = unfold_recursive_defns pctx f1 `Left in
  let pctx, f2, _ = unfold_recursive_defns pctx f2 `Right in
  (pctx, f1, f2)

let simplify : total =
 fun (pctx, f1, f2) ->
  let@ _ =
    span (fun r -> log_proof_state_total ~title:"simplify" (pctx, f1, f2) r)
  in
  (pctx, normalize_spec f1, normalize_spec f2)

let apply_induction_hypotheses : total =
  let open Rewriting in
  let open Rules.Staged in
  fun ps ->
    let@ _ =
      span (fun r ->
          log_proof_state_total ~title:"apply_induction_hypotheses" ps r)
    in
    let pctx, f1, f2 = ps in
    let db =
      pctx.induction_hypotheses
      |> List.filter (fun (n, _) -> has_been_unfolded pctx n `Left)
    in
    debug ~at:4 ~title:"can be unfolded?" "%s"
      (string_of_list Fun.id (List.map fst db));
    let db = db |> List.map snd in
    let f1 = autorewrite db (Staged f1) |> of_uterm in
    (pctx, f1, f2)

let apply_lemmas : total =
  let open Rewriting in
  let open Rules.Staged in
  fun ps ->
    let@ _ = span (fun r -> log_proof_state_total ~title:"apply_lemmas" ps r) in
    let pctx, f1, f2 = ps in
    let f1 = autorewrite pctx.lemmas (Staged f1) |> of_uterm in
    (pctx, f1, f2)

let create_induction_hypothesis (ps : pstate) : pctx =
  let@ _ =
    span (fun _r -> log_proof_state ~title:"create_induction_hypothesis" ps)
  in
  let pctx, f1, f2 = ps in
  let name = match f1 with HigherOrder (f, _) -> Some f | _ -> None in
  match name with
  | None -> pctx
  | Some name ->
    let free =
      SSet.union (Subst.free_vars f1) (Subst.free_vars f2)
      |> SSet.remove "res" (* this isn't a free var; it's bound by ens *)
      |> SSet.remove name (* the function itself isn't free *)
      |> SSet.to_list
    in
    (* assume they are of term type *)
    let bs = List.map (fun f -> (f, Rewriting.Rules.Term.uvar f)) free in
    let f3 = Subst.subst_free_vars bs f1 in
    let f4 = Subst.subst_free_vars bs f2 in
    let ih = Rewriting.Rules.Staged.rule f3 f4 in
    { pctx with induction_hypotheses = (name, ih) :: pctx.induction_hypotheses }

let is_recursive pctx f =
  List.find_opt (fun (g, _) -> g = f) pctx.definitions_rec |> Option.is_some

let biab h1 h2 k =
  let open Biab in
  let open Syntax in
  let _h, a, f, ctx =
    let@ _ =
      span (fun r ->
          debug ~at:4 ~title:"ent: biab" "%s * %s |- %s * %s"
            (string_of_result
               (fun (_h, a, _f, _ctx) -> string_of_kappa (sep_conj a))
               r)
            (string_of_kappa h1) (string_of_kappa h2)
            (string_of_result
               (fun (_h, _a, f, ctx) ->
                 string_of_state (conj ctx.equalities, sep_conj f))
               r))
    in
    solve emp_biab_ctx h1 h2
  in
  let a = sep_conj a in
  let f = sep_conj f in
  let eqs = conj ctx.equalities in
  k ((True, a), (eqs, f))

let rec apply_ent_rule ?name : tactic =
 fun (pctx, f1, f2) k ->
  let open Syntax in
  match (f1, f2) with
  (* base case *)
  | NormalReturn (True, EmptyHeap), NormalReturn (True, EmptyHeap)
  | Require (True, EmptyHeap), Require (True, EmptyHeap) ->
    k (pctx, ens (), ens ())
  | ( Sequence (NormalReturn (True, EmptyHeap), f1),
      Sequence (NormalReturn (True, EmptyHeap), f2) )
  | ( Sequence (Require (True, EmptyHeap), f1),
      Sequence (Require (True, EmptyHeap), f2) ) ->
    entailment_search ?name (pctx, f1, f2) k
  (* proving *)
  | NormalReturn (p1, h1), NormalReturn (p2, h2) ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: ens ens" (pctx, f1, f2))
    in
    let@ (ap, ah), (fp, fh) = biab h1 h2 in
    let valid =
      check_pure_obligation
        (conj (pctx.assumptions @ [p1; ap; Heap.xpure h1]))
        (conj [p2; fp; Heap.xpure h2])
    in
    if valid then entailment_search ?name (pctx, req ~h:ah (), req ~h:fh ()) k
  | Require (p1, h1), Require (p2, h2) ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: req req" (pctx, f1, f2))
    in
    apply_ent_rule ?name (pctx, NormalReturn (p2, h2), NormalReturn (p1, h1)) k
  | Sequence (NormalReturn (p1, h1), f3), Sequence (NormalReturn (p2, h2), f4)
    ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: ens ens f" (pctx, f1, f2))
    in
    let@ (ap, ah), (fp, fh) = biab h1 h2 in
    let valid =
      check_pure_obligation
        (conj (pctx.assumptions @ [p1; ap; Heap.xpure h1]))
        (conj [p2; fp; Heap.xpure h2])
    in
    if valid then
      entailment_search ?name
        (pctx, seq [req ~h:ah (); f3], seq [req ~h:fh (); f4])
        k
  | Sequence (Require (p1, h1), f3), Sequence (Require (p2, h2), f4) ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: req req f" (pctx, f1, f2))
    in
    apply_ent_rule ?name
      (pctx, seq [NormalReturn (p2, h2); f3], seq [NormalReturn (p1, h1); f4])
      k
  (* create induction hypothesis *)
  | HigherOrder (f, _), f2
    when is_recursive pctx f && not (has_been_unfolded pctx f `Left) ->
    let ps =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: create IH, unfold" (pctx, f1, f2))
      in
      let pctx = create_induction_hypothesis (pctx, f1, f2) in
      let f1 = unfold_nonrecursive_defns pctx.definitions_nonrec f1 in
      let pctx, f1, _ = unfold_recursive_defns pctx f1 `Left in
      simplify (pctx, f1, f2)
    in
    entailment_search ?name ps k
  (* moving pure things into the context *)
  | ( Sequence
        ( NormalReturn
            (Atomic (EQ, Var lname, TLambda (_h, ps, Some sp, _body)), EmptyHeap),
          f3 ),
      f4 )
  | ( Bind
        ( lname,
          NormalReturn
            (Atomic (EQ, Var "res", TLambda (_h, ps, Some sp, _body)), EmptyHeap),
          f3 ),
      f4 ) ->
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: lambda binding" (pctx, f1, f2))
      in
      let rule = lambda_to_rule lname ps sp in
      { pctx with definitions_nonrec = rule :: pctx.definitions_nonrec }
    in
    entailment_search ?name (pctx, f3, f4) k
  | Sequence (NormalReturn (p1, EmptyHeap), f3), f2 ->
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: pure assumption" (pctx, f1, f2))
      in
      { pctx with assumptions = p1 :: pctx.assumptions }
    in
    entailment_search ?name (pctx, f3, f2) k
  | f1, Sequence (Require (p2, EmptyHeap), f4) ->
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: pure assumption" (pctx, f1, f2))
      in
      { pctx with assumptions = p2 :: pctx.assumptions }
    in
    entailment_search ?name (pctx, f1, f4) k
  (* quantifiers. intro before trying to instantiate *)
  | Exists (x, f3), f2 ->
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: exists on the left" (pctx, f1, f2))
      in
      { pctx with constants = Var x :: pctx.constants }
    in
    entailment_search ?name (pctx, f3, f2) k
  | f1, ForAll (x, f4) ->
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: forall on the right" (pctx, f1, f2))
      in
      { pctx with constants = Var x :: pctx.constants }
    in
    entailment_search ?name (pctx, f1, f4) k
  | f1, Exists (x, f4) ->
    let choices =
      pctx.constants
      |> List.map (fun c ->
             let f4 = Subst.subst_free_vars [(x, c)] f4 in
             fun k1 ->
               let@ _ =
                 span (fun _r ->
                     log_proof_state
                       ~title:
                         (Format.asprintf "ent: exists on the right; [%s/%s]"
                            (string_of_term c) x)
                       (pctx, f1, f2))
               in
               entailment_search ?name (pctx, f1, f4) k1)
    in
    disj_ choices k
  | ForAll (x, f3), f2 ->
    let choices =
      pctx.constants
      |> List.map (fun c ->
             let f3 = Subst.subst_free_vars [(x, c)] f3 in
             fun k1 ->
               let@ _ =
                 span (fun _r ->
                     log_proof_state
                       ~title:
                         (Format.asprintf "ent: forall on the left; [%s/%s]"
                            (string_of_term c) x)
                       (pctx, f1, f2))
               in
               entailment_search ?name (pctx, f3, f2) k1)
    in
    disj_ choices k
  (* disjunction *)
  | Disjunction (f3, f4), f2 ->
    let tag = Variables.fresh_variable () in
    let@ _ =
      span (fun _r ->
          debug ~at:4 ~title:(Format.asprintf "disj on the left [[%s]]" tag) "")
    in
    let@ _ = entailment_search ?name (pctx, f3, f2) in
    let@ _ =
      span (fun _r ->
          debug ~at:4 ~title:(Format.asprintf "right disjunct <<%s>>" tag) "")
    in
    entailment_search ?name (pctx, f4, f2) k
  | f1, Disjunction (f3, f4) ->
    debug ~at:4 ~title:"disj on the right" "";
    or_
      (let@ _ = span (fun _r -> debug ~at:4 ~title:"left disjunct" "") in
       entailment_search ?name (pctx, f1, f3))
      (let@ _ = span (fun _r -> debug ~at:4 ~title:"right disjunct" "") in
       entailment_search ?name (pctx, f1, f4))
      k
  | _, _ ->
    let ps = (pctx, f1, f2) in
    let ps1 =
      let@ _ =
        span (fun _r -> debug ~at:4 ~title:"try to unfold definitions" "")
      in
      unfold_definitions (pctx, f1, f2)
    in
    if ps <> ps1 then entailment_search ?name ps1 k
    else
      let ps1 =
        let@ _ = span (fun _r -> debug ~at:4 ~title:"try to apply IH" "") in
        apply_induction_hypotheses ps
      in
      if ps <> ps1 then entailment_search ?name ps1 k
      else
        let ps1 =
          let@ _ =
            span (fun _r -> debug ~at:4 ~title:"try to apply other lemmas" "")
          in
          apply_lemmas ps
        in
        if ps <> ps1 then entailment_search ?name ps1 k
        else (
          log_proof_state ~title:"STUCK" ps;
          fail)

and entailment_search : ?name:string -> tactic =
  let prev_state = ref None in
  fun ?name ps k ->
    (* Search.reset (); *)
    (* cycle detection for debugging *)
    if !prev_state = Some ps then failwith "cycle!" else prev_state := Some ps;
    let ps = simplify ps in
    apply_ent_rule ?name ps k

let check_staged_spec_entailment ?name pctx inferred given =
  let@ _ =
    span (fun r ->
        debug ~at:2 ~title:"entailment" "%s\n⊑\n%s\n%s"
          (string_of_staged_spec inferred)
          (string_of_staged_spec given)
          (string_of_result string_of_bool r))
  in
  match Iter.head (entailment_search ?name (pctx, inferred, given)) with
  | None -> false
  | Some ps ->
    debug ~at:2 ~title:"proof found" "%s" (string_of_pstate ps);
    true

(*
let unfolding_bound = 1

type fvenv = Forward_rules.fvenv

let with_pure pi ((p, h) : state) : state = (conj [p; pi], h)
let rename_exists_spec sp = List.hd (Forward_rules.renamingexistientalVar [Untypehip.untype_spec sp]) |> Fill_type.fill_untyped_spec

let rename_exists_lemma (lem : lemma) : lemma =
  { lem with l_right = rename_exists_spec lem.l_right }

let rename_exists_pred (pred : pred_def) : pred_def =
  { pred with p_body = Forward_rules.renamingexistientalVar (Untypehip.untype_disj_spec pred.p_body) |> Fill_type.fill_untyped_disj_spec}
*)

(* module Heap = struct
  (*
  let normalize : state -> state =
   fun (p, h) ->
    let h = simplify_heap (Untypehip.untype_kappa h) in
    (simplify_pure (Untypehip.untype_pi p) |> Fill_type.fill_untyped_pi, h |> Fill_type.fill_untyped_kappa)
  *)
  (** given a nonempty heap formula, splits it into a points-to expression and
      another heap formula *)

  let rec split_one (h : kappa) : (kappa * kappa) option =
    match h with
    | EmptyHeap -> None
    | PointsTo _ -> Some (h, EmptyHeap)
    | SepConj (a, b) -> begin
      match split_one a with
      | None -> split_one b
      | Some (c, r) -> Some (c, SepConj (r, b))
    end

  (*
  (** like split_one, but searches for a particular points-to *)
  let rec split_find : binder -> kappa -> (term * kappa) option =
   fun n h ->
    match h with
    | EmptyHeap -> None
    | PointsTo (x, v) when x = (ident_of_binder n) -> Some (v, EmptyHeap)
    | PointsTo _ -> None
    | SepConj (a, b) -> begin
      match split_find n a with
      | None ->
        split_find n b |> Option.map (fun (t, b1) -> (t, SepConj (a, b1)))
      | Some (t, a1) -> Some (t, SepConj (a1, b))
    end

  let pairwise_var_inequality v1 v2 =
    List.concat_map
      (fun x ->
        List.filter_map
          (fun y ->
            if x = y then None
            else Some (Not (Atomic (EQ, var_from_binder x, var_from_binder y))))
          v2)
      v1
    |> conj
  *)

  (* this is utility, should we moved outside this module
  let xpure : kappa -> pi =
   fun h ->
    let rec run h =
      match h with
      | EmptyHeap -> (True, [])
      | PointsTo (x, _t) -> (Atomic (GT, {term_desc = Var x; term_type = Int}, {term_desc = Const (Num 0); term_type = Int}), [])
      | SepConj (a, b) ->
        let a, v1 = run a in
        let b, v2 = run b in
        (And (a, And (b, pairwise_var_inequality v1 v2)), [])
    in
    let p, _vs = run h in
    p
  *)
end *)

(*
let check_staged_entail : spec -> spec -> spec option =
 fun n1 n2 ->
  let norm = normalize_spec (n1 @ n2 |> Untypehip.untype_spec) in
  Some (normalisedStagedSpec2Spec norm) |> Option.map Fill_type.fill_untyped_spec

let instantiate_state bindings state =
  let bindings = Untypehip.untype_bindings bindings in
  let (p, h) = Untypehip.untype_state state in
  (instantiatePure bindings p, instantiateHeap bindings h)

let instantiate_existentials_effect_stage bindings =
  let names = List.map fst bindings in
  fun eff ->
   {
      eff with
      e_evars = List.filter (fun v -> not (List.mem v names)) eff.e_evars;
      e_pre = instantiate_state bindings eff.e_pre |> Fill_type.fill_untyped_state;
      e_post = instantiate_state bindings eff.e_post |> Fill_type.fill_untyped_state;
      e_constr =
        ( fst eff.e_constr,
          (List.map (instantiateTerms (Untypehip.untype_bindings bindings))) (snd eff.e_constr |> List.map Untypehip.untype_term) |> List.map Fill_type.fill_untyped_term);
      e_ret = instantiateTerms (Untypehip.untype_bindings bindings) (Untypehip.untype_term eff.e_ret) |> Fill_type.fill_untyped_term;
    }

(** actually instantiates existentials, vs what the forward rules version does *)
let instantiate_existentials :
    (binder * term) list -> normalisedStagedSpec -> normalisedStagedSpec =
 fun bindings (efs, ns) ->
  let names = List.map fst bindings in
  let (efs:effectStage list) =
    List.fold_left (fun acc a ->
    let temp = match a with
    | EffHOStage ele -> [ele]
    | _ -> []
    in
    acc @ temp) [] efs
  in
  let efs1 = List.map (instantiate_existentials_effect_stage bindings) efs in
  let ns1 =
    let vs, pre, post = ns in
    ( List.filter (fun v -> not (List.mem v names)) vs |> List.map ident_of_binder,
      instantiate_state bindings pre,
      instantiate_state bindings post)
  in
  (List.map (fun a -> EffHOStage a) efs1, Fill_type.fill_untyped_normal_stage ns1)

let freshen_existentials vs state =
  let vars_fresh = List.map (fun v -> (v, (verifier_getAfreeVar v |> var_from_binder))) vs in
  (vars_fresh, instantiate_state vars_fresh state)

(** Given two heap formulae, matches points-to predicates.
  may backtrack if the locations are quantified.
  returns (by invoking the continuation) when matching is complete (when right is empty).

  id: human-readable name
  vs: quantified variables
  k: continuation
*)
(* biabduction, should refactor *)
let rec check_qf :
    string ->
    binder list ->
    state ->
    state ->
    (pi * pi * kappa -> 'a Search.t) ->
    'a Search.t =
 fun id vs ante conseq k ->
  let open Search in
  (* TODO ptr equalities? *)
  let a = Heap.normalize ante in
  let c = Heap.normalize conseq in
  debug ~at:1
    ~title:(Format.asprintf "SL entailment (%s)" id)
    "%s |- %s" (string_of_state ante) (string_of_state conseq);
  (* TODO frame and spans *)
  match (a, c) with
  | (p1, h1), (p2, EmptyHeap) ->
    debug ~at:4 ~title:(Format.asprintf "right empty") "";
    let left = And (Heap.xpure h1, p1) in
    (* TODO add more logging to surface what happens in these entailments *)
    k (left, p2, h1)
  | (p1, h1), (p2, h2) -> begin
    (* we know h2 is non-empty *)
    match Heap.split_one h2 with
    | Some ((x, v), h2') when List.mem x vs ->
      debug ~at:4 ~title:(Format.asprintf "existential location %s" (string_of_binder x)) "";
      let left_heap = list_of_heap (Untypehip.untype_kappa h1) |> Fill_type.fill_untyped_bindings in
      (match left_heap with
      | [] -> fail
      | _ :: _ ->
        (* x is bound and could potentially be instantiated with anything on the right side, so try everything *)
        let r1 =
          any
            ~to_s:(fun (a, _) -> string_of_pair string_of_binder string_of_term a)
            ~name:"ent-match-any"
            (left_heap |> List.map (fun a -> (a, (x, v))))
            (fun ((x1, v1), _) ->
              let _v2, h1' = Heap.split_find x1 h1 |> Option.get in
              (* ptr equality *)
              let _ptr_eq = Atomic (EQ, var_from_binder x1, var_from_binder x) in
              let triv = Atomic (EQ, v, v1) in
              (* matching ptr values are added as an eq to the right side, since we don't have a term := term substitution function *)
              check_qf id vs (conj [p1], h1') (conj [p2; triv], h2') k)
        in
        r1)
    | Some ((x, v), h2') -> begin
      debug ~at:4 ~title:(Format.asprintf "free location %s" (string_of_binder x)) "";
      (* x is free. match against h1 exactly *)
      match Heap.split_find x h1 with
      | Some (v1, h1') -> begin
        check_qf id vs
          (conj [p1], h1')
          (conj [p2; And (p1, Atomic (EQ, v, v1))], h2')
          k
      end
      | None ->
        (* TODO *)
        debug ~at:4 ~title:(Format.asprintf "failed") "";
        fail
    end
    | None -> failwith (Format.asprintf "could not split LHS, bug?")
  end
*)
(* module Biabduction = struct *)
(* put biabduction stuffs here *)
(* end *)

(*
let instantiate_pred : pred_def -> term list -> term -> pred_def =
 fun pred args ret ->
  let@ _ =
    Debug.span (fun r ->
        debug ~at:4 ~title:"instantiate_pred" "%s\n%s\n%s\n==> %s"
          (string_of_pred pred)
          (string_of_list string_of_term args)
          (string_of_term ret)
          (string_of_result string_of_pred r))
  in
  (* the predicate should have one more arg than arguments given for the return value, which we'll substitute with the return term from the caller *)
  (* Format.printf "right before instantiate %s@." (string_of_pred pred); *)
  let pred = rename_exists_pred pred in
  (* Format.printf "rename exists %s@." (string_of_pred pred); *)
  let params, ret_param = unsnoc pred.p_params in
  let bs = (ret_param, ret) :: bindFormalNActual (*List.map2 (fun a b -> (a, b)) *) params args in
  let p_body =
    let bbody =
      (Untypehip.untype_disj_spec pred.p_body) |> List.map (fun b -> List.map (instantiateStages (Untypehip.untype_bindings bs)) b) |> Fill_type.fill_untyped_disj_spec
    in
    (* Format.printf "bs %s@."
         (string_of_list (string_of_pair Fun.id string_of_term) bs);
       Format.printf "pred.p_body %s@." (string_of_disj_spec pred.p_body);
       Format.printf "bbody %s@."
         (string_of_list (string_of_list string_of_staged_spec) bbody); *)
    bbody
  in
  { pred with p_body }

(* unfolding, should be moved to unfold.ml *)
let rec unfold_predicate_aux pred prefix (s : spec) : disj_spec =
  match s with
  | [] ->
    let r = List.map Acc.to_list prefix in
    r
  | HigherOrder (p, h, (name, args), ret) :: s1
    when String.equal name pred.p_name ->
    (* debug ~at:1
       ~title:(Format.asprintf "unfolding: %s" name)
       "%s" (string_of_pred pred); *)
    let pred1 = instantiate_pred pred args ret in
    (* debug ~at:1
       ~title:(Format.asprintf "instantiated: %s" name)
       "%s" (string_of_pred pred1); *)
    let prefix =
      prefix
      |> List.concat_map (fun p1 ->
             List.map
               (fun disj ->
                 p1 |> Acc.add (NormalReturn (p, h)) |> Acc.add_all disj)
               pred1.p_body)
    in
    unfold_predicate_aux pred prefix s1
  | c :: s1 ->
    let pref = List.map (fun p -> Acc.add c p) prefix in
    unfold_predicate_aux pred pref s1

(* let unfold_predicate : pred_def -> disj_spec -> disj_spec =
   fun pred ds ->
    List.concat_map (fun s -> unfold_predicate_aux pred [Acc.empty] s) ds *)

(** f;a;e \/ b and a == c \/ d
  => f;(c \/ d);e \/ b
  => f;c;e \/ f;d;e \/ b *)
let unfold_predicate_spec : string -> pred_def -> spec -> disj_spec =
 fun which pred sp ->
  let@ _ =
    Debug.span (fun r ->
        debug ~at:1
          ~title:(Format.asprintf "unfolding (%s): %s" which pred.p_name)
          "%s\nin\n%s\n==>\n%s" (string_of_pred pred) (string_of_spec sp)
          (string_of_result string_of_disj_spec r))
  in
  unfold_predicate_aux pred [Acc.empty] sp

let unfold_predicate_norm :
    string -> pred_def -> normalisedStagedSpec -> normalisedStagedSpec list =
 fun which pred sp ->
  List.map normalize_spec
    (unfold_predicate_spec which pred (normalisedStagedSpec2Spec (Untypehip.untype_normalized_staged_spec sp) |> Fill_type.fill_untyped_spec) |> List.map Untypehip.untype_spec)
  |> List.map Fill_type.fill_normalized_staged_spec
(* end unfolding *)

(** proof context *)
type pctx = {
  (* lemmas and predicates defined before (and usable by) the current function being verified *)
  lems : lemma SMap.t;
  preds : pred_def SMap.t;
  (* additional predicates due to local lambda definitions *)
  lambda_preds : pred_def SMap.t;
  (* all quantified variables in this formula *)
  q_vars : binder list;
  (* predicates which have been unfolded, used as an approximation of progress (in the cyclic proof sense) *)
  unfolded : (string * [ `Left | `Right ]) list;
  (* lemmas applied *)
  applied : string list;
  (* subsumption proof obligations *)
  subsumption_obl : (binder list * (disj_spec * disj_spec)) list;
}

let string_of_pctx ctx =
  Format.asprintf
    "lemmas: %s\n\
     predicates: %s\n\
     lambda predicates: %s\n\
     q_vars: %s\n\
     unfolded: %s\n\
     applied: %s\n\
     subsumption obligations: %s@."
    (string_of_smap string_of_lemma ctx.lems)
    (string_of_smap string_of_pred ctx.preds)
    (string_of_smap string_of_pred ctx.lambda_preds)
    (string_of_list string_of_binder ctx.q_vars)
    (string_of_list
       (string_of_pair Fun.id (function `Left -> "L" | `Right -> "R"))
       ctx.unfolded)
    (string_of_list Fun.id ctx.applied)
    (string_of_list string_of_pobl ctx.subsumption_obl)

let create_pctx lems preds q_vars =
  {
    lems;
    preds;
    lambda_preds = SMap.empty;
    q_vars;
    unfolded = [];
    applied = [];
    subsumption_obl = [];
  }

(* it's possible we may merge the same lambda into the map multiple times because we recurse after unfolding, which may have the lambda there again *)
let collect_local_lambda_definitions state ctx =
  let res =
    {
      ctx with
      lambda_preds =
        let defs = local_lambda_defs#visit_state () state in
        (* Format.printf "defs: %s@." (string_of_smap string_of_pred defs); *)
        SMap.merge_disjoint defs ctx.lambda_preds;
    }
  in
  res

let extract_subsumption_proof_obligations ctx right =
  let sub = find_subsumptions#visit_pi () right
    |> List.map (fun (lhs, rhs) -> Fill_type.(fill_untyped_term lhs, fill_untyped_term rhs)) in
  let right1 = (remove_subsumptions (List.map (fun (lhs, rhs) -> Untypehip.(untype_term lhs, untype_term rhs)) sub))#visit_pi () right in
  let sub = List.map (fun (t1, t2) ->
    match t1.term_desc, t2.term_desc with
    | TLambda (_, ap, _, _), TLambda (_, bp, _, _) when List.length ap <> List.length bp ->
      failwith (Format.asprintf "|%s| != |%s|" (string_of_list string_of_binder ap) (string_of_list string_of_binder bp));
    | TLambda (_, ap, a, _), TLambda (_, bp, b, _) ->
      let fv = List.map (fun _ -> verifier_getAfreeVar "v") ap in
      let a1 = instantiateSpecList (List.map2 (fun v x -> ident_of_binder v, Untypehip.untype_term (var_from_binder x)) ap fv) (Untypehip.untype_disj_spec a) |> Fill_type.fill_untyped_disj_spec in
      let b1 = instantiateSpecList (List.map2 (fun v x -> ident_of_binder v, Untypehip.untype_term (var_from_binder x)) bp fv) (Untypehip.untype_disj_spec b) |> Fill_type.fill_untyped_disj_spec in
      fv, (a1, b1)
    | _ -> failwith (Format.asprintf "unable to check obligation %s <: %s" (string_of_term t1) (string_of_term t2))) sub
  in
  right1, { ctx with subsumption_obl = sub @ ctx.subsumption_obl }

(** Given two normalized flows, checks their head stages for subsumption,
    then recurses down, propagating residue and updating the proof context
    with things like local predicate definitions.

    Matching of existentially-quantified locations (in SL entailments)
    may cause backtracking.
    Other existentials are handled by the SMT back end.
*)
let rec check_staged_subsumption_stagewise :
    pctx ->
    int ->
    pi ->
    normalisedStagedSpec ->
    normalisedStagedSpec ->
    pctx Search.t =
 fun ctx i assump s1 s2 ->
 (*print_endline ("check_staged_subsumption_stagewise");*)


  debug ~at:1 ~title:"flow subsumption" "%s\n<:\n%s"
    (string_of_normalisedStagedSpec s1)
    (string_of_normalisedStagedSpec s2);
  let open Search in
  match (s1, s2) with
  | (EffHOStage es1 :: es1r, ns1), (EffHOStage es2 :: es2r, ns2) ->
    (*print_endline ("check_staged_subsumption_stagewise case one ");*)
    let ctx =
      ctx |> collect_local_lambda_definitions es2.e_pre
        |> collect_local_lambda_definitions es1.e_post
    in
    (* fail fast by doing easy checks first *)
    let c1, a1 = es1.e_constr in
    let c2, a2 = es2.e_constr in
    (match String.equal c1 c2 with
    | false ->
      let@ _ =
        try_other_measures ctx s1 s2 (Some c1) (Some c2) i assump |> or_else
      in
      debug ~at:1 ~title:"FAIL" "constr %s != %s" c1 c2;
      fail
    | true ->
      let* _ =
        let l1 = List.length a1 in
        let l2 = List.length a2 in
        let r = l1 = l2 in
        if not r then (
          debug ~at:1 ~title:"FAIL" "arg length %s (%d) != %s (%d)"
            (string_of_list string_of_term a1)
            l1
            (string_of_list string_of_term a2)
            l2;
          fail)
        else succeed
      in
      (* done with easy checks, start proving *)
      (* pure information propagates forward across stages, not heap info *)
      let* residue, ctx =
        let arg_eqs = conj (List.map2 (fun x y -> Atomic (EQ, x, y)) a1 a2) in
        (*print_endline ("stage_subsumes recursive");*)

        let temp = stage_subsumes ctx
          (Format.asprintf "effect stage %d" i)
          assump
          (es1.e_evars, (es1.e_pre, with_pure (res_eq es1.e_ret) es1.e_post))
          ( es2.e_evars,
            (es2.e_pre, with_pure (And (arg_eqs, res_eq es2.e_ret)) es2.e_post)
          )
        in
        temp
      in
      (*print_endline ("check_staged_subsumption_stagewise recursive");*)
      check_staged_subsumption_stagewise ctx (i + 1)
        (conj [assump; residue])
        (es1r, ns1) (es2r, ns2))

  | (TryCatchStage tc1 :: _es1r, _ns1), (TryCatchStage tc2 :: _es2r, _ns2) ->
    (*print_endline ("entailement checking with two catches"); *)
    let src1, _ = tc1.tc_constr in
    let src2, _ = tc2.tc_constr in

    let es1, ns1 = normalize_spec (Untypehip.untype_spec src1) |> Fill_type.fill_normalized_staged_spec in
    let es2, ns2 = normalize_spec (Untypehip.untype_spec src2) |> Fill_type.fill_normalized_staged_spec in
    check_staged_subsumption_stagewise ctx 0 True (es1, ns1) (es2, ns2)
    (* Ask Darius *)


  | ([], ns1), ([], ns2) ->
    (* base case: check the normal stage at the end *)
    let (vs1, (p1, h1), (qp1, qh1 as post1)) = ns1 in
    let (vs2, ((p2, h2) as pre2), (qp2, qh2)) = ns2 in
    let ctx =
      ctx |> collect_local_lambda_definitions post1
        |> collect_local_lambda_definitions pre2
    in
    let* _residue, pctx =
      stage_subsumes ctx "normal stage" assump
        (vs1, ((p1, h1), (qp1, qh1)))
        (vs2, ((p2, h2), (qp2, qh2)))
    in
    ok pctx
  | ([], n1), (EffHOStage es2 :: _, _) ->
    let ctx =
      let _ex, _pre, n1post = n1 in
      ctx |> collect_local_lambda_definitions n1post
        |> collect_local_lambda_definitions es2.e_pre
    in
    let c2, _ = es2.e_constr in
    let@ _ = try_other_measures ctx s1 s2 None (Some c2) i assump |> or_else in
    debug ~at:1 ~title:"FAIL" "ante is shorter\n%s\n<:\n%s"
      (string_of_normalisedStagedSpec s1)
      (string_of_normalisedStagedSpec s2);
      (*print_endline("fail 486");*)
    fail
  | (EffHOStage es1 :: _, _), ([], n1) ->
    (* we are allowed to find lambdas in:
       - the pre of the right side (as it will eventually make it down via a frame)
       - the post of the left side *)
    let ctx =
      let _ex, n1pre, _post = n1 in
      ctx |> collect_local_lambda_definitions n1pre
        |> collect_local_lambda_definitions es1.e_post
    in
    let c1, _ = es1.e_constr in
    let@ _ = try_other_measures ctx s1 s2 (Some c1) None i assump |> or_else in
    debug ~at:1 ~title:"FAIL" "conseq is shorter\n%s\n<:\n%s"
      (string_of_normalisedStagedSpec s1)
      (string_of_normalisedStagedSpec s2);
      (*print_endline("fail 495");*)
    fail

  | _  ->fail


and try_other_measures :
    pctx ->
    normalisedStagedSpec ->
    normalisedStagedSpec ->
    string option ->
    string option ->
    int ->
    pi ->
    pctx Search.t =
  let open Search in
  fun ctx s1 s2 c1 c2 i assump ->
    (* first try to unfold on the left. it works if there is something to unfold (the current stage must be a function/effect, and there is a corresponding definition in the predicate environment) *)
    match
      let* c1 = c1 in
      let+ res =
        let@ _ = SMap.find_opt c1 ctx.preds |> or_else in
        SMap.find_opt c1 ctx.lambda_preds
      in
      (c1, res)
    with
    | Some (c1, def)
      (* always allow unfolding of non-recursive predicates *)
      when List.length (List.filter (fun s -> s = (c1, `Left)) ctx.unfolded)
           < unfolding_bound || not def.p_rec ->
      let unf = unfold_predicate_norm "left" def s1 in
      let@ s1_1, ctx =
        all_state ~name:(Format.asprintf "unfold lhs: %s" c1)~to_s:string_of_normalisedStagedSpec ~init:ctx ~pivot:(fun c -> { ctx with subsumption_obl = c.subsumption_obl }) unf
      in
      check_staged_subsumption_stagewise
        { ctx with unfolded = (c1, `Left) :: ctx.unfolded }
        i assump s1_1 s2
    | _ ->
      (* if that fails, try to unfold on the right *)
      (match
         let* c2 = c2 in
         let+ res =
           let@ _ = SMap.find_opt c2 ctx.preds |> or_else in
           SMap.find_opt c2 ctx.lambda_preds
         in
         (c2, res)
       with
      | Some (c2, pred_def)
       (* always allow unfolding of non-recursive predicates *)
        when List.length (List.filter (fun s -> s = (c2, `Right)) ctx.unfolded)
             < unfolding_bound || not pred_def.p_rec ->
        let unf = unfold_predicate_norm "right" pred_def s2 in
        let@ s2_1 =
          any ~name:(Format.asprintf "unfold rhs: %s" c2)~to_s:string_of_normalisedStagedSpec unf
        in
        check_staged_subsumption_stagewise
          { ctx with unfolded = (c2, `Right) :: ctx.unfolded }
          i assump s1 s2_1
      | _ ->
        (* if that fails, try to apply a lemma. note that this is the reason we can't use Search.any action, as we only apply lemmas once unfolding is no longer possible, presumably because it has been done already. this approximates an inductive decreasing-arguments check *)
        let eligible =
          ctx.lems |> SMap.bindings
          |> List.filter (fun (ln, _l) -> not (List.mem ln ctx.applied))
          |> List.filter (fun (_ln, l) -> List.mem (fst l.l_left, `Left) ctx.unfolded)
          (* prevent rewriting unless unfolding of the left side has taken place. this works for the IH, but not for lemmas in general *)
          |> List.map snd
        in
        let s1_1, applied =
          apply_one_lemma eligible (Fill_type.fill_untyped_spec (normalisedStagedSpec2Spec (Untypehip.untype_normalized_staged_spec s1)))
        in
        applied
        |> Option.iter (fun l ->
               debug ~at:1
                 ~title:(Format.asprintf "apply %s" l.l_name)
                 "%s\n\nafter:\n%s\n<:\n%s" (string_of_lemma l)
                 (string_of_spec s1_1)
                 (string_of_normalisedStagedSpec s2));
        (match applied with
        | Some app ->
          check_staged_subsumption_stagewise
            { ctx with applied = app.l_name :: ctx.applied }
            i assump (normalize_spec (Untypehip.untype_spec s1_1) |> Fill_type.fill_normalized_staged_spec) s2
        | None ->
          (* no predicates to try unfolding *)
          let pp c =
            match c with
            | Some f -> Format.asprintf "effect stage %s" f
            | None -> Format.asprintf "normal stage"
          in
          debug ~at:1
            ~title:
              (Format.asprintf "ran out of tricks to make %s and %s match"
                 (pp c1) (pp c2))
            "%s" (string_of_pctx ctx);
          fail))

and stage_subsumes :
    pctx ->
    string ->
    pi ->
    (state * state) quantified ->
    (state * state) quantified ->
    (pi * pctx) Search.t =
 fun ctx what assump s1 s2 ->
  let open Search in
  let vs1, (pre1, post1) = s1 in
  let vs2, (pre2, post2) = s2 in
  (* TODO replace uses of all_vars. this is for us to know if locations on the rhs are quantified. a smaller set of vars is possible *)
  let@ _ =
    Debug.span (fun r ->
      debug ~at:1
        ~title:(Format.asprintf "subsumption for %s" what)
        "%s * (%sreq %s; ens %s)\n<:\n(%sreq %s; ens %s)\n==>\n%s" (string_of_pi assump)
        (string_of_existentials vs1)
        (string_of_state pre1) (string_of_state post1)
        (string_of_existentials vs2)
        (string_of_state pre2) (string_of_state post2)
        (string_of_result (fun o -> string_of_bool (Option.is_some o)) r))
  in
  (* contravariance *)
  let@ pre_l, pre_r, pre_resi_l = check_qf "pre" ctx.q_vars pre2 pre1 in
  let* pre_residue, tenv, ctx =
    let left = conj [assump; pre_l] in
    let right = pre_r in
    let left = Normalize.simplify_pure (Untypehip.untype_pi left) |> Fill_type.fill_untyped_pi in
    let right = Normalize.simplify_pure (Untypehip.untype_pi right) |> Fill_type.fill_untyped_pi in
    let@ _ =
      Debug.span (fun r ->
          debug ~at:2
            ~title:(Format.asprintf "VC for precondition of %s" what)
            "%s => %s%s\n\nvalid? %s" (string_of_pi left)
            (string_of_existentials vs1)
            (string_of_pi right)
            (string_of_result (fun o -> string_of_bool (Option.is_some o)) r))
    in
    let tenv =
      (* handle the environment manually as it's shared between both sides *)
      let env = create_abs_env () in
      let env = infer_types_pi env (Untypehip.untype_pi left) in
      let env = infer_types_pi env (Untypehip.untype_pi right) in
      env
    in
    let right, ctx = extract_subsumption_proof_obligations ctx (Untypehip.untype_pi right) in
    (* debug ~at:1
      ~title:(Format.asprintf "VC for precondition of %s" what)
      "%s => %s%s" (string_of_pi left)
      (string_of_existentials vs1)
      (string_of_pi right); *)
    let pre_res =
      Provers.entails_exists (concrete_type_env tenv) (Untypehip.untype_pi left) (List.map ident_of_binder vs1) right
    in
    (* debug ~at:1 ~title:(Format.asprintf "valid?") "%s" (string_of_res pre_res); *)
    (* TODO why do we need pre_r here? as pre_l has just been proven to subsume pre_r *)
    if pre_res then Some ((conj [pre_l; pre_r; assump], pre_resi_l), tenv, ctx)
    else None
  in
  (* covariance *)
  let new_univ = SSet.union (used_vars_pi (Untypehip.untype_pi pre_l)) (used_vars_pi (Untypehip.untype_pi pre_r)) in
  let vs22 = List.filter (fun v -> not (SSet.mem v new_univ)) (List.map ident_of_binder vs2) |> List.map binder_of_ident in
  let conj_state (p1, h1) (p2, h2) = (And (p1, p2), SepConj (h1, h2)) in
  let pure_pre_residue = fst pre_residue in
  let@ post_l, post_r, _post_resi =
    check_qf "post" ctx.q_vars (conj_state pre_residue post1) post2
  in
  let* post_residue, ctx =
    (* don't use fresh variable for the ret value so it carries forward in the residue *)
    (* let _a, r = split_res_fml post_l in *)
    (* let left = conj [fst pre_residue; post_l] in *)
    (* let right = conj [post_r; r] in *)
    let left = conj [fst pre_residue; post_l] in
    let right = conj [post_r] in
    let left = Normalize.simplify_pure (Untypehip.untype_pi left) |> Fill_type.fill_untyped_pi in
    let right = Normalize.simplify_pure (Untypehip.untype_pi right) |> Fill_type.fill_untyped_pi in
    let@ _ =
      Debug.span (fun r ->
          debug ~at:2
            ~title:(Format.asprintf "VC for postcondition of %s" what)
            "%s => %s%s\n\nvalid? %s" (string_of_pi left)
            (string_of_existentials vs22)
            (string_of_pi right)
            (string_of_result (fun o -> string_of_bool (Option.is_some o)) r))
    in
    let tenv =
      (* let env = infer_types_pi tenv left in *)
      (* let env = infer_types_pi env right in *)
      (* share things like res *)
      let env = infer_types_pi tenv (And ((Untypehip.untype_pi left), (Untypehip.untype_pi right))) in
      env
    in
    (* Format.printf "1@."; *)
    (* Format.printf "left %s@." (string_of_pi left); *)
    (* let tenv1 = concrete_type_env tenv in *)
    (* Format.printf "2@."; *)
    (* Format.printf "tenv %s@." (string_of_smap string_of_type tenv1); *)
    (* let _check_false_derived _ =
      debug ~at:1
        ~title:(Format.asprintf "check: false derived?")
        "%s" (string_of_pi left);
      let false_not_derived = Provers.askZ3 tenv1 left in
      debug ~at:1 ~title:(Format.asprintf "false") "%s" (string_of_pi left);
      if not false_not_derived then
        (* since the program is usually on the left, false on the left side of the postcondition means this *)
        debug ~at:1
          ~title:(Format.asprintf "warning: false derived in program")
          "%s => %s%s\n%s" (string_of_pi True) "" (string_of_pi left)
          (string_of_res false_not_derived)
    in *)
    let right, ctx = extract_subsumption_proof_obligations ctx (Untypehip.untype_pi right) in
    let right = Fill_type.fill_untyped_pi right in
    (* debug ~at:1
      ~title:(Format.asprintf "VC for postcondition of %s" what)
      "%s => %s%s" (string_of_pi left)
      (string_of_existentials vs22)
      (string_of_pi right); *)
    let post_result =
      Provers.entails_exists (concrete_type_env tenv) (Untypehip.untype_pi left) (List.map ident_of_binder vs22) (Untypehip.untype_pi right)
    in
    (*print_endline ((string_of_pi left) ^ " |- " ^ (string_of_pi right));
    print_endline ("post_result is done ");
    print_endline (string_of_bool post_result);
    *)

    (* debug ~at:1 ~title:(Format.asprintf "valid?") "%s" (string_of_res post_result); *)
    (* TODO ensure we are filling out f with the correct type *)
    let f = verifier_getAfreeVar "" in
    let left = instantiatePure [("res", var_from_binder f |> Untypehip.untype_term)] (Untypehip.untype_pi left) |> Fill_type.fill_untyped_pi in
    let right = instantiatePure [("res", var_from_binder f |> Untypehip.untype_term)] (Untypehip.untype_pi right) |> Fill_type.fill_untyped_pi in
    (* let left = fst (split_res left) in *)
    (* let right = fst (split_res left) in *)
    if post_result then Some (conj [left; right; pure_pre_residue], ctx) else None
  in

  ok (conj [pure_pre_residue; post_residue], ctx)

let rec apply_tactics ts lems preds (ds1 : disj_spec) (ds2 : disj_spec) =
  List.fold_left
    (fun t c ->
      let ds1, ds2 = t in
      let r =
        match c with
        | Unfold_right ->
          debug ~at:1 ~title:"unfold left" "%s" ((string_of_smap string_of_pred) preds);
          (* let ds2 = SMap.fold (fun _n -> unfold_predicate) preds ds2 in *)
          (ds1, ds2)
        | Unfold_left ->
          debug ~at:1 ~title:"unfold left" "%s" (string_of_smap string_of_pred preds);
          (* let ds1 = SMap.fold (fun _n -> unfold_predicate) preds ds1 in *)
          (ds1, ds2)
        | Case (i, ta) ->
          (* case works on the left only *)
          debug ~at:1 ~title:"case" "%d" i;
          let ds, _ = apply_tactics [ta] lems preds [List.nth ds1 i] ds2 in
          (* unfolding (or otherwise adding disjuncts) inside case will break use of hd *)
          let ds11 = replace_nth i (List.hd ds) ds1 in
          (ds11, ds2)
        | Apply l ->
          (* apply works on the left only *)
          debug ~at:1 ~title:"apply" "%s" l;
          failwith "apply tactic needs to be updated"
        (* ( List.map
             (List.fold_right apply_lemma
                (List.filter (fun le -> String.equal le.l_name l) lems))
             ds1,
           ds2 ) *)
      in
      debug ~at:1 ~title:"after" "%s\n<:\n%s"
        (string_of_disj_spec (fst r))
        (string_of_disj_spec (snd r));
      r)
    (ds1, ds2) ts

let create_induction_hypothesis params ds1 ds2 =
  let fail fmt =
    Format.kasprintf
      (fun s ->
        debug ~at:1 ~title:"no induction hypothesis" "%s" s;
        None)
      fmt
  in
  match (ds1, ds2) with
  | [s1], [s2] ->
    let ns1 = s1 |> normalize_spec |> Fill_type.fill_normalized_staged_spec in
    let used_l = used_vars (Untypehip.untype_normalized_staged_spec ns1) in
    (* heuristic. all parameters must be used meaningfully, otherwise there's nothing to do induction on *)
    (match List.for_all (fun p -> SSet.mem (ident_of_binder p) used_l) params with
    | true ->
      (match ns1 with
      | [EffHOStage eff], (_, (True, EmptyHeap), (post, EmptyHeap))
        when is_just_res_of post eff.e_ret ->
        (* when r = eff.e_ret *)
        (* TODO existentials are ignored...? *)
        let f, a = eff.e_constr in
        let res = binder_of_ident "res" in
        let ih =
          {
            l_name = "IH";
            l_params = params @ [res];
            l_left = (f, a @ [var_from_binder res]);
            l_right = s2;
          }
        in
        debug ~at:1 ~title:"induction hypothesis" "%s" (string_of_lemma ih);
        Some ih
      | [_], _ -> fail "nontrivial norm stage after"
      | _ -> fail "lhs not just a single stage")
    | false ->
      fail "not all params used by lhs of entailment: params %s, %s used"
        (string_of_list string_of_binder params)
        (string_of_sset used_l))
  | _ -> fail "left side disjunctive"
*)

(*
 fun mname params _ts lems preds ds1 ds2 ->
  Search.reset ();
  debug ~at:1
    ~title:(Format.asprintf "disj subsumption: %s" mname)
    "%s\n<:\n%s" (string_of_disj_spec ds1) (string_of_disj_spec ds2);
  let ih = create_induction_hypothesis params (Untypehip.untype_disj_spec ds1) ds2 in
  let lems =
    match ih with None -> lems | Some ih -> SMap.add ih.l_name ih lems
  in
  let ctx = create_pctx lems preds [] in
  (* let ds1, ds2 = apply_tactics ts lems preds ds1 ds2 in *)
  let@ s1, ctx = Search.all_state ~name:"disj lhs" ~to_s:string_of_spec ~init:ctx ~pivot:(fun c -> { ctx with subsumption_obl = c.subsumption_obl }) ds1 in
  let@ s2 = Search.any ~name:"disj rhs" ~to_s:string_of_spec ds2 in
  (* S1 <: S3 *)
  let es1, ns1 = normalize_spec (Untypehip.untype_spec s1) |> Fill_type.fill_normalized_staged_spec in
  let es2, ns2 = normalize_spec (Untypehip.untype_spec s2) |> Fill_type.fill_normalized_staged_spec in
  let q_vars = getExistentialVar (Untypehip.untype_normalized_staged_spec (es1, ns1)) @ getExistentialVar (Untypehip.untype_normalized_staged_spec (es2, ns2)) |> List.map binder_of_ident in
  let ctx = { ctx with q_vars } in
  check_staged_subsumption_stagewise ctx 0 True (es1, ns1) (es2, ns2)
*)
