open Hipcore_typed
open Typedhip
open Pretty
open With_types
open Hipcore.Common
open Hipcore.Types
open Debug
open Utils

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
  lemmas : (string * Rewriting.rule) list;
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
    (string_of_list_ind_lines (string_of_pair Fun.id string_of_rule) lemmas)
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

let has_induction_hypothesis pctx name =
  pctx.induction_hypotheses
  |> List.find_opt (fun (u, _) -> u = name)
  |> Option.is_some

let term_uvar_of_binder b =
  Rewriting.Rules.Term.uvar (ident_of_binder b) ~typ:(type_of_binder b)

let type_vars_of_params params =
  params
  |> List.map (fun p -> Hipcore.Types.free_type_vars (type_of_binder p) |> SSet.of_list)
  |> SSet.concat
  |> SSet.to_list

let uvar_bindings ?(type_subs = []) binders =
    binders
    |> List.map (fun p -> (ident_of_binder p,
      Rewriting.Rules.Term.uvar (ident_of_binder p) ~typ:(type_of_binder p |> Subst.subst_types_in_type type_subs)))

let pred_to_rule pred =
  (* Replace the type variables in the parameters with uvars. *)
  let type_vars_in_pred = type_vars_of_params pred.p_params in
  let type_uvars = type_vars_in_pred
    |> List.map (fun tv -> (tv, Rewriting.Rules.Type.uvar tv)) in
  (* Replace the parameters of the predicate with uvars. *)
  let params = pred.p_params |> List.map term_uvar_of_binder |> List.map (Subst.subst_types Sctx_term type_uvars) in
  let lhs = HigherOrder (pred.p_name, params) in
  let rhs =
    let bs = uvar_bindings ~type_subs:type_uvars pred.p_params
    in
    pred.p_body
    |> Subst.subst_free_vars bs
    |> Subst.subst_types Sctx_staged type_uvars
  in
  (pred.p_name, Rewriting.Rules.Staged.rule lhs rhs)

let lemma_to_rule lemma =
  let type_vars = type_vars_of_params lemma.l_params in
  let type_uvar_bindings = type_vars |> List.map (fun tv -> (tv, Rewriting.Rules.Type.uvar tv)) in
  let bs = uvar_bindings ~type_subs:type_uvar_bindings lemma.l_params in
  let lhs = Subst.subst_free_vars bs lemma.l_left |> Subst.subst_types Sctx_staged type_uvar_bindings in
  let rhs = Subst.subst_free_vars bs lemma.l_right |> Subst.subst_types Sctx_staged type_uvar_bindings in
  (lemma.l_name, Rewriting.Rules.Staged.rule lhs rhs)

let create_pctx cp =
  let definitions_nonrec =
    SMap.values cp.cp_predicates
    |> List.filter (fun p -> not p.p_rec)
    |> List.map pred_to_rule
  in
  let lemmas = SMap.values cp.cp_lemmas |> List.map lemma_to_rule in
  let definitions_rec =
    SMap.values cp.cp_predicates
    |> List.filter (fun p -> p.p_rec)
    |> List.map pred_to_rule
  in
  { (new_pctx ()) with definitions_nonrec; definitions_rec; lemmas }

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
  let left, right =
    let@ _ = span (fun _r -> debug ~at:4 ~title:"simplify before" "") in
    (Simpl.simplify_pure left, Simpl.simplify_pure right)
  in
  let@ _ =
    span (fun r ->
        debug ~at:4 ~title:"check_pure_obligation" "%s => %s ? %s"
          (string_of_pi left) (string_of_pi right)
          (string_of_result string_of_bool r))
  in
  (* There may be unifications not known to the type checker, due to things like
     the untyped extensions. Perform another typechecking phase to perform these
     unifications. *)
  let (left, right), _ =
    let open Infer_types in
    with_empty_env begin
      let* left, right = infer_types_pair_pi left right in
      return (left, right)
    end
  in
  let res = Provers.entails_exists left [] right in
  let open Provers_common in
  debug ~at:4 ~title:"prover detailed result" "%s" (string_of_prover_result res);
  match res with
  | Valid -> true
  | _ -> false

(* will be used for remembering predicate? Not sure whether it should be put here *)
let derive_predicate m_name m_params f =
  let new_spec = Normalize.normalize_spec f in
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

let try_constants pctx = Syntax.[num 0; term (Const Nil) (TConstr ("list", [Any]))] @ pctx.constants

(** Tactics combine the state and list monads *)
module Tactic : sig
  type 'a t = pstate -> ('a * pstate) Iter.t

  val run : 'a t -> pstate -> pctx option
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ctx : pctx t

  type goal = staged_spec * staged_spec

  val goal : goal t
  val goal_lhs : staged_spec t
  val goal_rhs : staged_spec t
  val with_lhs : staged_spec -> (unit -> 'a t) -> 'a t
  val with_rhs : staged_spec -> (unit -> 'a t) -> 'a t
  val fail : 'a t
  val choice : 'a t -> 'a t -> 'a t
  val choices : 'a t list -> 'a t
  val committed_choice : 'a t -> 'a t -> 'a t
  val committed_choices : 'a t list -> 'a t

  val failure :
    title:string -> ('a, Format.formatter, unit, unit t) format4 -> 'a

  val span :
    'a t -> title:string -> ('b, Format.formatter, unit, 'a t) format4 -> 'b
end = struct
  (* [@@@warning "-unused-value-declaration"] *)

  type 'a t = pstate -> ('a * pstate) Iter.t
  type goal = staged_spec * staged_spec

  let run t ps = Iter.head (t ps) |> Option.map (fun (_, (pctx, _, _)) -> pctx)
  let fail = fun _ -> Iter.empty
  let return x = fun s -> Iter.return (x, s)
  let bind m f = fun s -> Iter.flat_map (fun (x, s') -> f x s') (m s)
  let ( let* ) = bind
  let get = fun s -> Iter.return (s, s)

  let ctx =
    let* r, _, _ = get in
    return r

  let goal =
    let* _, f1, f2 = get in
    return (f1, f2)

  let goal_lhs =
    let* _, f1, _ = get in
    return f1

  let goal_rhs =
    let* _, _, f2 = get in
    return f2

  let put s = fun _ -> Iter.return ((), s)

  let put_lhs f1 =
    let* pctx, _, f2 = get in
    put (pctx, f1, f2)

  let put_rhs f2 =
    let* pctx, f1, _ = get in
    put (pctx, f1, f2)

  let put_goal (f1, f2) =
    let* pctx, _, _ = get in
    put (pctx, f1, f2)

  (* let with_ (pctx, f1, f2) t =
    let* _ = put (pctx, f1, f2) in
    t () *)

  let with_lhs f1 t =
    let* of1, of2 = goal in
    let* () = put_lhs f1 in
    let* r = t () in
    let* () = put_goal (of1, of2) in
    return r

  let with_rhs f2 t =
    let* of1, of2 = goal in
    let* () = put_rhs f2 in
    let* r = t () in
    let* () = put_goal (of1, of2) in
    return r

  let choice t1 t2 = fun ps -> Iter.append (t1 ps) (t2 ps)
  let choices ts = fun ps -> Iter.append_l (List.map (fun t -> t ps) ts)

  (* like ltac's lazymatch. unsure if this is necessary as we only get one solution. also this may lead to incompleteness of search, as we cannot backtrack past this, like a cut? *)
  let committed_choice (t1 : 'a t) (t2 : 'a t) : 'a t =
   fun ps -> Iter.take 1 ((choice t1 t2) ps)

  let committed_choices ts = fun ps -> Iter.take 1 ((choices ts) ps)

  let failure ~title fmt =
    Format.kasprintf
      (fun msg ->
        fun s k ->
         Debug.debug ~at:4 ~title "%s" msg;
         fail s k)
      fmt

  let span (t : 'a t) ~title fmt =
    Format.kasprintf
      (fun msg ->
        fun s k ->
         let@ _ = span (fun _r -> Debug.debug ~at:4 ~title "%s" msg) in
         t s k)
      fmt
end

type coq_tactic =
  | Rewrite of string
  | SRReduction
  | Simplify
  | Biab
  | EntDisjL
  | EntDisjR
  | Focus of coq_tactic list

type coq_tactics = coq_tactic list

let rec string_of_coq_tactic t =
  match t with
  | EntDisjL -> "apply ent_disj_l."
  | EntDisjR -> "apply ent_disj_l."
  | Focus [] -> ""
  | Focus [a] -> Format.asprintf "{ %s }" (string_of_coq_tactic a)
  | Focus (a :: rest) ->
    Format.asprintf "{ %s\n%s }" (string_of_coq_tactic a)
      (string_of_list_ind_lines string_of_coq_tactic rest)
  | Simplify -> "fsimpl."
  | Biab -> "fbiabduction."
  | SRReduction -> "freduction."
  | Rewrite r -> Format.asprintf "rewrite %s." r

and string_of_coq_tactics ts =
  ts |> List.map string_of_coq_tactic |> String.concat "\n"

let%expect_test _ =
  Format.printf "%s@."
    (string_of_coq_tactics
       [
         EntDisjL;
         Focus
           [
             EntDisjR;
             EntDisjL;
             EntDisjR;
             EntDisjL;
             EntDisjR;
             EntDisjL;
             EntDisjR;
             EntDisjL;
           ];
         Focus [EntDisjR];
       ]);
  [%expect
    {|
    apply ent_disj_l.
    { apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l. }
    { apply ent_disj_l. }
    |}]

let rec disj_left () : unit Tactic.t =
  let open Tactic in
  let* left = goal_lhs in
  match left with
  | Disjunction (f1, f2) ->
    let* _ = span (with_lhs f1 search) ~title:"disj left" "left branch" in
    span (with_lhs f2 search) ~title:"disj left" "right branch"
  | _ -> fail

and disj_right () : unit Tactic.t =
  let open Tactic in
  let* right = goal_rhs in
  match right with
  | Disjunction (f1, f2) ->
    let goal2 = span (with_rhs f2 search) ~title:"disj right" "right branch" in
    let goal1 = span (with_rhs f1 search) ~title:"disj right" "left branch" in
    choice goal1 goal2
  | _ -> fail

and ens_ens () : unit Tactic.t =
  let open Tactic in
  let* left, right = goal in
  match (left, right) with
  | NormalReturn (True, EmptyHeap), NormalReturn (True, EmptyHeap) ->
    debug ~at:4 ~title:"ens ens" "ok";
    return ()
  | _ -> fail

and search () : unit Tactic.t =
  let open Tactic in
  let* left, right = goal in
  debug ~at:4 ~title:"search" "%s |- %s"
    (string_of_staged_spec left)
    (string_of_staged_spec right);
  choices [disj_left (); disj_right (); ens_ens (); failure ~title:"STUCK" ""]

let%expect_test _ =
  Debug.test_init 4;
  let open Syntax in
  let left = Disjunction (ens (), ens ()) in
  let right = Disjunction (ens ~p:False (), ens ()) in
  let r = Tactic.run (search ()) (new_pctx (), left, right) |> Option.get in
  debug ~at:4 ~title:"done" "%s" (string_of_pstate (r, left, right));
  [%expect
    {|
    * search | _1
    (ens emp) \/ (ens emp) |- (ens F) \/ (ens emp)

    * disj left | _2
    left branch

    ** search | _3
    ens emp |- (ens F) \/ (ens emp)

    ** disj right | _4
    left branch

    *** search | _5
    ens emp |- ens F

    *** STUCK | _6

    *** disj right | _7 <-_4
    left branch

    ** disj right | _8
    right branch

    *** search | _9
    ens emp |- ens emp

    *** ens ens | _10
    ok

    *** disj left | _11
    right branch

    **** search | _12
    ens emp |- (ens F) \/ (ens emp)

    **** disj right | _13
    left branch

    ***** search | _14
    ens emp |- ens F

    ***** STUCK | _15

    ***** disj right | _16 <-_13
    left branch

    **** disj right | _17
    right branch

    ***** search | _18
    ens emp |- ens emp

    ***** ens ens | _19
    ok

    ***** disj right | _20 <-_17
    right branch

    **** disj left | _21 <-_11
    right branch

    *** disj right | _22 <-_8
    right branch

    ** disj left | _23 <-_2
    left branch

    * done | _24
    (ens emp) \/ (ens emp)
    ⊑
    (ens F) \/ (ens emp)
    <============================================================
    constants:
    []

    induction_hypotheses:


    lemmas:


    assumptions:


    definitions_nonrec:


    definitions_rec:


    unfolded:
    |}]

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

let unfold_nonrecursive_definitions ((pctx, f1, f2) : pstate) : pstate =
  let f1 = unfold_nonrecursive_defns pctx.definitions_nonrec f1 in
  let f2 = unfold_nonrecursive_defns pctx.definitions_nonrec f2 in
  (pctx, f1, f2)

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

let rec repeat_simplify_lhs ?(limit = 5) (spec : staged_spec) : staged_spec =
  if limit < 0 then failwith "repeat_simplify_lhs: loop?";
  let simple_spec = Reduce_shift_reset.shift_reset_reduce_spec_lhs spec in
  let simple_spec = Normalize.normalize_spec_lhs simple_spec in
  if simple_spec = spec then spec else repeat_simplify_lhs ~limit:(limit - 1) simple_spec

let simplify : total =
 fun (pctx, f1, f2) ->
  let@ _ =
    span (fun r -> log_proof_state_total ~title:"simplify" (pctx, f1, f2) r)
  in
  let pctx, f1, f2 = unfold_nonrecursive_definitions (pctx, f1, f2) in
  let f1 = repeat_simplify_lhs f1 in
  let f2 = Normalize.normalize_spec_rhs f2 in
  (pctx, f1, f2)

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
    let lemmas = List.map snd pctx.lemmas in
    (* TODO nondet application, as multiple may apply.
      currently only the first applies and may disable the others *)
    let f1 = autorewrite lemmas (Staged f1) |> of_uterm in
    (pctx, f1, f2)

let create_induction_hypothesis (ps : pstate) name : pctx =
  let@ _ =
    span (fun _r -> log_proof_state ~title:"create_induction_hypothesis" ps)
  in
  let pctx, f1, f2 = ps in
  let free =
    SSet.union Subst.(free_vars Sctx_staged f1) Subst.(free_vars Sctx_staged f2)
    |> SSet.remove "res" (* this isn't a free var; it's bound by ens *)
    |> SSet.remove name (* the function itself isn't free *)
  in
  (* names of previous definitions are not free variables *)
  let remove_definition set (def, _) = SSet.remove def set in
  let free = List.fold_left remove_definition free pctx.definitions_nonrec in
  let free = List.fold_left remove_definition free pctx.definitions_rec in
  let free = SSet.to_list free in
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
  let _h, a, f, eqs =
    let@ _ =
      span (fun r ->
          debug ~at:4 ~title:"ent: biab" "%s * %s |- %s * %s"
            (string_of_result
               (fun (_h, a, _f, _eqs) -> string_of_kappa (sep_conj a))
               r)
            (string_of_kappa h1) (string_of_kappa h2)
            (string_of_result
               (fun (_h, _a, f, eqs) -> string_of_state (conj eqs, sep_conj f))
               r))
    in
    solve emp_biab_ctx h1 h2
  in
  let a = sep_conj a in
  let f = sep_conj f in
  let eqs = conj eqs in
  k ((eqs, a), (True, f))

let biab' h1 h2 k =
  let open Biab in
  let open Syntax in
  let _h, a, f, eqs =
    let@ _ =
      span (fun r ->
          debug ~at:4 ~title:"ent: biab" "%s * %s |- %s * %s"
            (string_of_result
               (fun (_h, a, _f, _eqs) -> string_of_kappa (sep_conj a))
               r)
            (string_of_kappa h1) (string_of_kappa h2)
            (string_of_result
               (fun (_h, _a, f, eqs) -> string_of_state (conj eqs, sep_conj f))
               r))
    in
    solve emp_biab_ctx h1 h2
  in
  k (a, f, eqs)

let add_assumption (pctx : pctx) (p : pi) =
  match p with
  | True -> pctx
  | _ -> {pctx with assumptions = p :: pctx.assumptions}

let prove_pure_fact (pctx : pctx) (p : pi) =
  match p with
  | True -> true
  | False -> false
  | _ -> check_pure_obligation (Syntax.conj pctx.assumptions) p

let rec handle_pure_ens_lhs (pctx : pctx) (f : staged_spec) : pctx * staged_spec =
  debug ~at:5 ~title:"handle_pure_ens_lhs" "%s " (string_of_staged_spec f);
  match f with
  | NormalReturn (p, EmptyHeap) when not (Variables.is_eq_res p) ->
      add_assumption pctx p, NormalReturn (True, EmptyHeap)
  | Sequence (NormalReturn (p, EmptyHeap), f') when not (Variables.is_eq_res p) ->
      let pctx = add_assumption pctx p in
      handle_pure_ens_lhs pctx f'
  | ForAll (x, Sequence (NormalReturn (p, EmptyHeap), f'))
    when not (Variables.is_eq_res p) (* && x not in free(p) *) ->
      let pctx = add_assumption pctx p in
      handle_pure_ens_lhs pctx (ForAll (x, f'))
  | _ ->
      pctx, f

let rec handle_pure_ens_rhs (pctx : pctx) (f : staged_spec) : staged_spec option =
  debug ~at:5 ~title:"handle_pure_ens_rhs" "";
  match f with
  | NormalReturn (p, EmptyHeap) when not (Variables.is_eq_res p) ->
      if prove_pure_fact pctx p then Some (NormalReturn (True, EmptyHeap)) else None
  | Sequence (NormalReturn (p, EmptyHeap), f') when not (Variables.is_eq_res p) ->
      if prove_pure_fact pctx p then handle_pure_ens_rhs pctx f' else None
  | _ ->
      Some f

let suppress_exn ~title ~default (f : unit -> 'a) : 'a =
  try
    f ()
  with e ->
    debug ~at:5 ~title "%s" (Printexc.to_string e);
    default

let suppress_some_exn ~title ~default (f : unit -> 'a) : 'a =
  try
    f ()
  with
  | Z3.Error _ | Infer_types.Cyclic_type _ as e ->
      debug ~at:5 ~title "%s" (Printexc.to_string e);
      default

let rec apply_ent_rule ?name : tactic =
 fun (pctx, f1, f2) k ->
  let pctx, f1 = handle_pure_ens_lhs pctx f1 in
  let f2 = match handle_pure_ens_rhs pctx f2 with
    | None -> f2
    | Some f2 -> f2
  in
  let open Syntax in
  match (f1, f2) with
  (* base case *)
  | NormalReturn (True, EmptyHeap), NormalReturn (True, EmptyHeap)
  | Require (True, EmptyHeap), Require (True, EmptyHeap) ->
    (* | Require (True, EmptyHeap), Require (True, EmptyHeap) -> *)
    k (pctx, ens (), ens ())
  (* | ( Sequence (NormalReturn (True, EmptyHeap), f1),
      Sequence (NormalReturn (True, EmptyHeap), f2) )
  | ( Sequence (Require (True, EmptyHeap), f1),
      Sequence (Require (True, EmptyHeap), f2) ) ->
    entailment_search ?name (pctx, f1, f2) k *)
  (* move pure things into the context *)
  | ( Sequence
        ( NormalReturn
            (Atomic (EQ, {term_desc = Var lname; _}, {term_desc = TLambda (_h, ps, Some sp, _body); _}), EmptyHeap),
          f3 ),
      f4 )
  | ( Bind
        ( (lname, _),
          NormalReturn
            (Atomic (EQ, {term_desc = Var "res"; _}, {term_desc = TLambda (_h, ps, Some sp, _body); _}), EmptyHeap),
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
  | ( Sequence
        ( (NormalReturn _ as f_head),
          Bind
            ( (lname, _),
              NormalReturn
                ( Atomic (EQ, {term_desc = Var "res"; _}, {term_desc = TLambda (_h, ps, Some sp, _body); _}),
                  EmptyHeap ),
              f3 ) ),
      f4 ) ->
    (* TODO: do not copy code. Refactor this into a function *)
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: lambda binding" (pctx, f1, f2))
      in
      let rule = lambda_to_rule lname ps sp in
      { pctx with definitions_nonrec = rule :: pctx.definitions_nonrec }
    in
    entailment_search ?name (pctx, Sequence (f_head, f3), f4) k
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
  (* biabduction *)
  | Sequence (NormalReturn (p1, h1), Require (p2, h2)), f2 ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: biab" (pctx, f1, f2))
    in
    let@ (ap, ah), (fp, fh) = biab h1 h2 in
    let f1 =
      seq
        [
          Require (ap, ah);
          NormalReturn (fp, fh);
          NormalReturn (p1, EmptyHeap);
          Require (p2, EmptyHeap);
        ]
    in
    entailment_search ?name (pctx, f1, f2) k
  | Sequence (NormalReturn (p1, h1), Sequence (Require (p2, h2), f3)), f2 ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: biab f" (pctx, f1, f2))
    in
    let@ (ap, ah), (fp, fh) = biab h1 h2 in
    let f1 =
      seq
        [
          Require (ap, ah);
          NormalReturn (fp, fh);
          NormalReturn (p1, EmptyHeap);
          Require (p2, EmptyHeap);
          f3;
        ]
    in
    entailment_search ?name (pctx, f1, f2) k
  (* biabduction + instantiate forall *)
  | ( ForAll
        (y, Sequence (NormalReturn (p1, h1), Sequence (Require (p2, h2), f3))),
      f2 ) ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: biab f inst" (pctx, f1, f2))
    in
    let@ a, f, eqs = biab' h1 h2 in
    let find_equality = function
      | Atomic (EQ, t1, t2) when t1.term_desc = Var (ident_of_binder y) -> Some t2
      | Atomic (EQ, t1, t2) when t2.term_desc = Var (ident_of_binder y) -> Some t1
      | _ -> None
    in
    let f1 =
      match Lists.find_delete_map find_equality eqs with
      | None ->
        seq
          [
            Require (conj (p2 :: eqs), sep_conj a);
            NormalReturn (p1, sep_conj f);
            f3;
          ]
      | Some (t, eqs) ->
        debug ~at:5 ~title:"ent: biab f inst with" "[%s/%s]" (string_of_term t) (string_of_binder y);
        seq
          [
            Require (conj (p2 :: eqs), sep_conj a);
            NormalReturn (p1, sep_conj f);
            Subst.subst_free_vars [(ident_of_binder y, t)] f3;
          ]
    in
    entailment_search ?name (pctx, f1, f2) k
  (*
  | ( Sequence
        ( NormalReturn (p1, (PointsTo (_, v) as h1)),
          ForAll (y, Sequence (Require (p2, h2), f3)) ),
      f2 ) ->
    let@ _ =
      span (fun _r -> log_proof_state ~title:"ent: biab f inst" (pctx, f1, f2))
    in
    let@ (ap, ah), (fp, fh) = biab h1 h2 in
    let f1 =
      seq
        [
          Require (ap, ah);
          NormalReturn (fp, fh);
          NormalReturn (p1, EmptyHeap);
          Require (p2, EmptyHeap);
          Subst.subst_free_vars [(y, v)] f3;
        ]
    in
    entailment_search ?name (pctx, f1, f2) k *)
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
    if valid then begin
      debug ~at:5 ~title:"ent: ens ens valid" "";
      entailment_search ?name (pctx, req ~h:ah (), req ~h:fh ()) k
    end else
      debug ~at:5 ~title:"ent: ens ens not valid" ""
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
    let@ (ap, ah), (_fp, fh) = biab h1 h2 in
    let valid =
      check_pure_obligation
        (conj (pctx.assumptions @ [p1; Heap.xpure h1]))
        (conj [p2; ap; Heap.xpure h2])
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
      (fun k1 ->
        let@ _ = span (fun _r -> debug ~at:4 ~title:"left disjunct" "") in
        entailment_search ?name (pctx, f1, f3) k1)
      (fun k1 ->
        let@ _ = span (fun _r -> debug ~at:4 ~title:"right disjunct" "") in
        entailment_search ?name (pctx, f1, f4) k1)
      k
  (* two functions with equal terms *)
  | HigherOrder (f1, a1), HigherOrder (f2, a2)
    when f1 = f2 && List.length a1 = List.length a2 ->
    let eqs = List.map2 eq a1 a2 |> conj in
    let valid = check_pure_obligation (conj pctx.assumptions) eqs in
    if valid then k (pctx, ens (), ens ())
  (* create induction hypothesis *)
  | HigherOrder (f, _), f2
    when is_recursive pctx f
         && (not (has_been_unfolded pctx f `Left))
         && not (has_induction_hypothesis pctx f) ->
    let ps =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: create IH, unfold" (pctx, f1, f2))
      in
      let pctx = create_induction_hypothesis (pctx, f1, f2) f in
      let f1 = unfold_nonrecursive_defns pctx.definitions_nonrec f1 in
      let pctx, f1, _ = unfold_recursive_defns pctx f1 `Left in
      simplify (pctx, f1, f2)
    in
    entailment_search ?name ps k
  (* quantifiers. intro before trying to instantiate *)
  | Exists (x, f3), f2 ->
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: exists on the left" (pctx, f1, f2))
      in
      { pctx with constants = var_of_binder x :: pctx.constants }
    in
    entailment_search ?name (pctx, f3, f2) k
  | f1, ForAll (x, f4) ->
    let pctx =
      let@ _ =
        span (fun _r ->
            log_proof_state ~title:"ent: forall on the right" (pctx, f1, f2))
      in
      { pctx with constants = var_of_binder x :: pctx.constants }
    in
    entailment_search ?name (pctx, f1, f4) k
  | f1, Exists (x, f4) ->
    let choices =
      try_constants pctx
      |> List.map (fun c ->
          let@ _ = suppress_exn
            ~title:"ERROR: exists on the right, subst step"
            ~default:(fun _ -> fail)
          in
          if Hipcore.Types.can_unify_with c.term_type (type_of_binder x) then
          (* copy the binder's type to allow for polymorphic constants in try_constants *)
          let f4 = Subst.subst_free_vars [(ident_of_binder x, term c.term_desc (type_of_binder x))] f4 in
          fun k1 ->
            let@ _ = suppress_some_exn
              ~title:"ERROR: exists on the right, entailment step"
              ~default:fail
            in
            let@ _ =
              span (fun _r -> log_proof_state
                ~title:(Format.asprintf "ent: exists on the right; [%s/%s]" (string_of_term c) (string_of_binder x))
                (pctx, f1, f2))
            in
            entailment_search ?name (pctx, f1, f4) k1
          else (fun _ -> fail))
    in
    disj_ choices k
  | ForAll (x, f3), f2 ->
    let choices =
      try_constants pctx
      |> List.map (fun c ->
          let@ _ = suppress_exn
            ~title:"ERROR: forall on the left, subst step"
            ~default:(fun _ -> fail)
          in
          if Hipcore.Types.can_unify_with c.term_type (type_of_binder x) then
          let f3 = Subst.subst_free_vars [((ident_of_binder x), term c.term_desc (type_of_binder x))] f3 in
          fun k1 ->
            let@ _ = suppress_some_exn
              ~title:"ERROR: forall on the left, entailment step"
              ~default:fail
            in
            let@ _ =
              span (fun _r -> log_proof_state
                ~title:(Format.asprintf "ent: forall on the left; [%s/%s]" (string_of_term c) (string_of_binder x))
                (pctx, f1, f2))
            in
            entailment_search ?name (pctx, f3, f2) k1
          else (fun _ -> fail))
    in
    disj_ choices k
  (* bind, which requires alpha equivalence *)
  | Bind (x1, f3, f4), Bind (x2, f5, f6) ->
    let tag = Variables.fresh_variable () in
    let x3 = Variables.fresh_variable () in
    let@ _ =
      span (fun _r ->
          debug ~at:4
            ~title:(Format.asprintf "bind first expression [[%s]]" tag)
            "")
    in
    let@ pctx, _, _ = entailment_search ?name (pctx, f3, f5) in
    let@ _ =
      span (fun _r ->
          debug ~at:4
            ~title:(Format.asprintf "bind second expression <<%s>>" tag)
            "")
    in
    entailment_search ?name
      ( pctx,
        Subst.subst_free_vars [(ident_of_binder x1, var x3)] f4,
        Subst.subst_free_vars [(ident_of_binder x2, var x3)] f6 )
      k
  (* disjunction *)
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
        else
          let is_contradiction =
            let@ _ = span (fun _r -> debug ~at:4 ~title:"try to discharge via contradiction" "") in
            check_pure_obligation (conj pctx.assumptions) False
          in
          if is_contradiction
          then k (pctx, ens (), ens ())
          else (log_proof_state ~title:"STUCK" ps; fail)

and entailment_search : ?name:string -> tactic =
  let prev_state = ref None in
  fun ?name ps k ->
    (* Search.reset (); *)
    (* cycle detection for debugging *)
    if !prev_state = Some ps then failwith "cycle!" else prev_state := Some ps;
    let ps = simplify ps in
    let ps = apply_lemmas ps in
    apply_ent_rule ?name ps k

let check_staged_spec_entailment ?name pctx inferred given =
  let@ _ = Hipcore_typed.Globals.Timing.(time entail) in
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
