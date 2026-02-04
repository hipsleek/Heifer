open Core
open Core.Syntax
open Bindlib
open Pretty
open Util.Strings
open Tactic
open Util
open Syntax_util

let is_pure t =
  match t with
  | Emp | PointsTo _ | SepConj _ -> false
  | _ -> true

let is_heap t =
  match t with
  | Emp | PointsTo _ | SepConj _ -> true
  | _ -> false

let parse_term ts =
  let open Parsing.Parse in
  let* constants = get_constants in
  pure (parse_term ~ctx:constants ts)

let admit = () <$ pop_pctxt

let uncons_ens f =
  match f with
  | Sequence (Ensures p, rest) when is_pure p -> pure (p, rest)
  | Ensures p when is_pure p -> pure (p, Ensures Emp)
  | _ -> fail "cannot uncons pure ens"

let uncons_req f =
  match f with
  | Sequence (Requires p, rest) when is_pure p -> pure (p, rest)
  | Requires p when is_pure p -> pure (p, Requires Emp)
  | _ -> fail "cannot uncons pure req"

let get_subsumption =
  let* t = get_goal in
  match t with
  | Subsumes (lhs, rhs) -> pure (lhs, rhs)
  | _ -> fail (Format.asprintf "get_subsumption: %a" pp_term t)

let put_subsumption lhs rhs = put_goal (Subsumes (lhs, rhs))

let put_lhs lhs =
  let* _, rhs = get_subsumption in
  put_subsumption lhs rhs

let put_rhs rhs =
  let* lhs, _ = get_subsumption in
  put_subsumption lhs rhs

let get_lhs =
  let+ lhs, _ = get_subsumption in
  lhs

let get_rhs =
  let+ _, rhs = get_subsumption in
  rhs

let unwrap o e =
  match o with
  | None -> fail e
  | Some x -> pure x

let guard b e = if b then pure () else fail e

let all_goals tac =
 fun s ->
  let open Results.Monad in
  let rec loop = function
    | [] -> pure []
    | s :: ss ->
        let* s1 = Tactic.run_pstate tac s in
        let+ s2 = loop ss in
        Pstate.append s1 s2
  in
  let+ s = loop (Pstate.destruct s) in
  ((), s)

let semicolon1 tac1 tac2 =
  let* _ = tac1 in
  all_goals tac2

let semicolon tac1 tac2 =
 fun s ->
  let open Results.Monad in
  let s1, s2 = Pstate.focus s in
  let+ s1 = Tactic.run_pstate (semicolon1 tac1 tac2) s1 in
  Pstate.append s1 s2

let push_pure_goals goals =
  let* p = get_pctxt in
  let new_ps = List.map (fun g -> { p with goal = g }) goals in
  modify (Pstate.append new_ps)

let invoke_why3 goal =
  let* constants = get_constants in
  let+ assumptions = get_assumptions in
  let constants = Array.of_list (SMap.fold (fun _ c acc -> c :: acc) constants []) in
  let handle_assumption _ assumption goal =
    if Why3_prover.is_translatable assumption then Implies (assumption, goal) else goal
  in
  let why3_goal = SMap.fold handle_assumption assumptions goal in
  let why3_goal = unbox (Mk.forall (bind_mvar constants (box_term why3_goal))) in
  Why3_prover.prove ~show_goal:!Proof_options.show_why3_goal why3_goal

let solve_invoke_why3 goal =
  let* result = invoke_why3 goal in
  match result with
  | `Valid -> pure ()
  | _ -> fail "solve_invoke_why3: cannot solve goal"

module Pure = struct
  module Intro = struct
    let pre_ens_intro =
      let* rhs = get_rhs in
      let+ t1, t2 = unwrap (unseq_open_ensures_opt rhs) "pre_ens_intro: not ensures" in
      (t1, unwrap_term_opt t2)

    let pre_req_intro =
      let* rhs = get_rhs in
      let+ t1, t2 = unwrap (unseq_open_requires_opt rhs) "pre_req_intro: not requires" in
      (t1, unwrap_term_opt t2)

    (** UNSAFE: heap assumptions are linear, cannot be duplicated freely! *)
  end

  let ens_intro =
    let* t, rhs = Intro.pre_ens_intro in
    let* _ = put_rhs rhs in
    let* _ = dup_pctxt in
    put_goal t

  module Elim = struct
    let pre_ens_elim =
      let* lhs = get_lhs in
      let+ t1, t2 = unwrap (unseq_open_ensures_opt lhs) "pre_ens_elim: not ensures" in
      (t1, unwrap_term_opt t2)

    let pre_req_elim =
      let* lhs = get_lhs in
      let+ t1, t2 = unwrap (unseq_open_requires_opt lhs) "pre_req_elim: not requires" in
      (t1, unwrap_term_opt t2)
  end

  let ens_pure_elim name =
    let* t, lhs = Elim.pre_ens_elim in
    let* _ = guard (Simply_typed.is_prop t) "ens_pure_elim: not prop" in
    let* _ = add_assumption name t in
    put_lhs lhs

  let req_pure_intro name =
    let* t, rhs = Intro.pre_req_intro in
    let* _ = guard (Simply_typed.is_prop t) "req_pure_intro: not prop" in
    let* _ = add_assumption name t in
    put_rhs rhs

  let impl_intro name =
    let* g = get_goal in
    let* p, q = unwrap (open_implies_opt g) "impl_intro: not implies" in
    let* _ = add_assumption name p in
    put_goal q

  let intro_pure name =
    choices ~err:"intro_pure: failed" [impl_intro name; ens_pure_elim name; req_pure_intro name]

  let pre_pure_solver goal =
    let* _ = guard (Simply_typed.is_prop goal) "pre_pure_solver: not prop" in
    solve_invoke_why3 goal

  let pure_solver =
    let* goal = get_goal in
    let* _ = pre_pure_solver goal in
    () <$ pop_pctxt

  let req_pure_elim =
    let* t, lhs = Elim.pre_req_elim in
    let* _ = guard (Simply_typed.is_prop t) "req_pure_elim: not prop" in
    let* _ = pre_pure_solver t in
    put_lhs lhs

  let ens_pure_intro =
    let* t, rhs = Intro.pre_ens_intro in
    let* _ = guard (Simply_typed.is_prop t) "ens_pure_intro: not prop" in
    let* _ = pre_pure_solver t in
    put_rhs rhs

  let elim_pure = choices ~err:"elim_pure: failed" [req_pure_elim; ens_pure_intro]

  let revert_pure name =
    let* assumption = pop_assumption name in
    modify_goal (Tm.implies assumption)

  let clear_pure name = () <$ pop_assumption name
end

let ex_falso = Tactic.put_goal False

let forward hyp =
  let* assumption = get_assumption hyp in
  match assumption with
  | Implies (l, r) ->
      let* pc = pop_pctxt in
      let* _ = push_pctxt pc in
      let* _ = put_assumption hyp r in
      let* _ = push_pctxt pc in
      put_goal l
  | _ -> fail "forward should be applied to an implication"

let specialize name ts =
  let* ts = map_m parse_term ts <&> Array.of_list in
  (* TODO allow not exactly same length? *)
  let* assumption = pop_assumption name in
  match assumption with
  | Forall b -> add_assumption name (msubst b ts)
  | _ -> fail "not a prop that can be specialised"

let have ~name s =
  let* g = parse_term s in
  let* ps = pop_pctxt in
  let* _ = push_pctxt ps in
  let* _ = add_assumption name g in
  push_pctxt { ps with goal = g }

let case ~name s =
  let* p = parse_term s in
  let* pc = pop_pctxt in
  let* _ = push_pctxt pc in
  let* _ = add_assumption name (Unop (Not, p)) in
  let* _ = push_pctxt pc in
  add_assumption name p

let goal_is s =
  let* g = parse_term s in
  let* g1 = get_goal in
  match equal_term g g1 with
  | true -> pure ()
  | false -> failf "@[<v>goal was expected to be@,  %a@,but was:@,  %a@]" pp_term g pp_term g1

let qed =
  let* ps = get in
  match ps with
  | [] -> pure ()
  | _ -> fail "proof not finished"

let refl =
  let* lhs, rhs = get_subsumption in
  if equal_term lhs rhs then pop_pctxt else fail "refl: cannot close goal"

module Simpl = struct
  let simpl_beta = Tactic.modify_goal Simpl.simpl_beta
  let simpl = Tactic.modify_goal Simpl.simpl
  let shift_reset_reduce = Tactic.modify_goal Shift_reset.reduce
  let prenex_assoc = Tactic.modify_goal Prenex.prenex_assoc
end

let revert s =
  let* x = parse_term s in
  match x with
  | Var v ->
      let* pc = get_pctxt in
      let dependent =
        SMap.filter (fun _k a -> has_vars (TVSet.singleton v) a) pc.assumptions |> SMap.bindings
      in
      (match dependent with
      | (k, _) :: _ -> failf "assumption %s is dependent on %s, cannot revert" k (name_of v)
      | [] ->
          let constants = SMap.remove (name_of v) pc.constants in
          let rename_ctxt = Rename.Core.remove_name (name_of v) pc.rename_ctxt in
          let goal = Forall (unbox (bind_mvar [| v |] (box_term pc.goal))) in
          let pc1 = { pc with rename_ctxt; constants; goal } in
          put_pctxt pc1)
  | _ -> fail "cannot revert non-var"

let forall_intro =
  let intro g k =
    match Prenex.prenex_head g with
    | Forall b ->
        let* ctxt = get_rename_ctxt in
        (* TODO freshness issues? this has to be free on both sides *)
        let xs, f, ctxt = Rename.unmbind_in ctxt b in
        let* _ = k f in
        let* _ = put_rename_ctxt ctxt in
        iter_array_m (fun x -> add_constant (name_of x) x) xs
    | _ -> fail "not a forall"
  in
  let staged =
    let* _, right = get_subsumption in
    intro right put_rhs
  in
  let pure =
    let* g = get_goal in
    intro g put_goal
  in
  choices [staged; pure]

let forall_elim t =
  let* left, _ = get_subsumption in
  match Prenex.prenex_head left with
  | Forall b ->
      let* t = map_m parse_term t <&> Array.of_list in
      put_lhs (msubst b t)
  | _ -> fail "cannot eliminate forall"

let exists_intro t =
  let* _, right = get_subsumption in
  match Prenex.prenex_head right with
  | Exists b ->
      let* t = map_m parse_term t <&> Array.of_list in
      put_rhs (msubst b t)
  | _ -> fail "cannot intro exists"

let exists_elim =
  let* ctxt = get_rename_ctxt in
  let* left, _ = get_subsumption in
  match Prenex.prenex_head left with
  | Exists b ->
      let xs, f, ctxt = Rename.unmbind_in ctxt b in
      let* _ = put_lhs f in
      let* _ = put_rename_ctxt ctxt in
      iter_array_m (fun x -> add_constant (name_of x) x) xs
  | _ -> fail "cannot eliminate exists"

module Conj = struct
  let conj_elim f_proj =
    let* lhs = get_lhs in
    let* lhs = unwrap (open_conj_opt lhs) "conj_elim: not conj" in
    put_lhs (f_proj lhs)

  let conj_elim_l = conj_elim fst
  let conj_elim_r = conj_elim snd

  let conj_intro =
    let open Tactic in
    let* rhs = get_rhs in
    let* rhs1, rhs2 = unwrap (open_conj_opt rhs) "conj_intro: not conj" in
    let* _ = put_rhs rhs2 in
    let* _ = dup_pctxt in
    put_rhs rhs1
end

module Disj = struct
  let disj_elim =
    let* lhs = get_lhs in
    let* lhs1, lhs2 = unwrap (open_disj_opt lhs) "disj_elim: not disj" in
    let* _ = put_lhs lhs2 in
    let* _ = dup_pctxt in
    put_lhs lhs1

  let disj_intro f_proj =
    let* rhs = get_rhs in
    let* rhs = unwrap (open_disj_opt rhs) "disj_intro: not disj" in
    put_rhs (f_proj rhs)

  let left = disj_intro fst
  let right = disj_intro snd
end

module Heaps = struct
  let ens_heap_elim =
    let* t, lhs = Pure.Elim.pre_ens_elim in
    let* ts = unwrap (Heap.deep_destruct_sepconj_opt t) "ens_heap_elim: not hprop" in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_lhs lhs

  let req_heap_intro =
    let* t, rhs = Pure.Intro.pre_req_intro in
    let* ts = unwrap (Heap.deep_destruct_sepconj_opt t) "req_heap_intro: not hprop" in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_rhs rhs

  let intro_heap = choices ~err:"intro_heap: failed" [ens_heap_elim; req_heap_intro]

  let unseq_open_opt f target =
    let open Util.Options.Monad in
    let* t, target = f target in
    let+ ts = Heap.deep_destruct_sepconj_opt t in
    (ts, target)

  let rec unseq_open_loop f target =
    match unseq_open_opt f target with
    | None -> ([], target)
    | Some (ts1, target) ->
        let ts2, target = unseq_open_loop f (unwrap_term_opt target) in
        (ts1 @ ts2, target)

  let ens_heap_elims =
    let* lhs = get_lhs in
    let ts, lhs = unseq_open_loop unseq_open_ensures_opt lhs in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_lhs lhs

  let req_heap_intros =
    let* rhs = get_rhs in
    let ts, rhs = unseq_open_loop unseq_open_requires_opt rhs in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_rhs rhs

  let intros_heap =
    let* _ = ens_heap_elims in
    let* _ = req_heap_intros in
    pure ()

  let pre_heap_solver goal =
    let goals_opt = Heap.deep_destruct_sepconj_opt goal in
    let* goals = unwrap goals_opt "pre_heap_solver: not hprop" in
    let* heap_assumptions = get_heap_assumptions in
    let goals, heap_assumptions, equalities = Heap.biab_list goals heap_assumptions in
    let* _ = guard (List.is_empty goals) "pre_heap_solver: cannot prove hprop" in
    let* _ = iter_m solve_invoke_why3 equalities in
    put_heap_assumptions heap_assumptions

  let heap_solver =
    let* goal = get_goal in
    let* _ = pre_heap_solver goal in
    () <$ pop_pctxt

  let req_heap_elim =
    let* t, lhs = Pure.Elim.pre_req_elim in
    let* _ = pre_heap_solver t in
    put_lhs lhs

  let ens_heap_intro =
    let* t, rhs = Pure.Intro.pre_ens_intro in
    let* _ = pre_heap_solver t in
    put_rhs rhs

  let elim_heap = choices ~err:"elim_heap: failed" [req_heap_elim; ens_heap_intro]

  let revert_heap =
    let* heap_assumptions = get_heap_assumptions in
    let* lhs = get_lhs in
    let* _ = put_heap_assumptions [] in
    put_lhs (Sequence (Ensures (Constr.sepconj heap_assumptions), lhs))
end

module Unmix = struct
  let unmix_ens f_get f_put =
    let* t = f_get in
    let* t1, t2 = unwrap (unseq_open_ensures_opt t) "unmix_ens: not ensures" in
    let pure, heap = Mixed.normalize_mixed t1 in
    let t2 = if is_emp heap then t2 else Some (reseq (Ensures heap) t2) in
    let t2 = if is_true pure then t2 else Some (reseq (Ensures pure) t2) in
    f_put (unwrap_term_opt t2)

  let unmix_ens_lhs = unmix_ens get_lhs put_lhs
  let unmix_ens_rhs = unmix_ens get_rhs put_rhs

  let unmix_req f_get f_put =
    let* t = f_get in
    let* t1, t2 = unwrap (unseq_open_requires_opt t) "unmix_req: not requires" in
    let pure, heap = Mixed.normalize_mixed t1 in
    let t2 = if is_emp heap then t2 else Some (reseq (Requires heap) t2) in
    let t2 = if is_true pure then t2 else Some (reseq (Requires pure) t2) in
    f_put (unwrap_term_opt t2)

  let unmix_req_lhs = unmix_req get_lhs put_lhs
  let unmix_req_rhs = unmix_req get_rhs put_rhs

  let unmix =
    let* _ = try_ unmix_req_lhs in
    let* _ = try_ unmix_ens_lhs in
    let* _ = try_ unmix_req_rhs in
    let* _ = try_ unmix_ens_rhs in
    pure ()
end

let rewrite direction stmt =
  let open Rewrite in
  let do_rewrite rule f_get f_put =
    let* target = f_get in
    (* Format.printf "rewrite target %a@." pp_term target; *)
    try
      let result, conditions = rewrite rule target in
      (* Format.printf "rewrite result %a conditions %a@." pp_term result (Fmt.list pp_term)
          conditions; *)
      let* _ = f_put result in
      let* _ = push_pure_goals conditions in
      pure ()
    with Rewrite_failure msg -> fail msg
  in
  let rule = make_rule ~direction stmt in
  let relation = get_rule_relation rule in
  let f_get, f_put =
    match (relation, direction) with
    | Relation_eq, _ -> (get_goal, put_goal)
    | Relation_subsumes, `Ltr -> (get_lhs, put_lhs)
    | Relation_subsumes, `Rtl -> (get_rhs, put_rhs)
  in
  do_rewrite rule f_get f_put

let prove =
  let prove_with_ctx p =
    let* assumptions = get_assumptions in
    let p =
      let ass =
        SMap.bindings assumptions |> List.map snd |> List.filter Why3_prover.is_translatable
      in
      List.fold_right (fun c t -> Implies (c, t)) ass p
    in
    let* free = get_constants in
    let entail =
      let free = free |> SMap.bindings |> List.map snd |> Array.of_list in
      unbox (Mk.forall (bind_mvar free (box_term p)))
    in
    let res = Why3_prover.prove ~show_goal:!Proof_options.show_why3_goal entail in
    (match res with
    | `Valid -> Format.printf "==> Valid\n@."
    | `Invalid -> Format.printf "==> Invalid\n@."
    | `Unknown s ->
        Format.printf "==> Unknown: %s\n@." s
        (* | `Failure s -> Format.printf "==> Failure: %s\n@." s *));
    pure res
  in
  let both_values =
    let could_be_value t =
      match t with
      | Var _ | True | False | Unit | Int _ | Apply _ -> true
      | _ -> false
    in
    let* left, right = get_subsumption in
    match could_be_value left && could_be_value right with
    | false -> fail "not values"
    | true ->
        let* res = prove_with_ctx (Binop (Eq, left, right)) in
        (match res with
        | `Valid ->
            let* _ = pop_pctxt in
            pure ()
        | _ -> fail "could not prove equality")
  in
  let can_be_translated =
    (* this is more general than the value case *)
    (* TODO is it possible that this produces props, which should then be related using implies? *)
    let* left, right = get_subsumption in
    match Why3_prover.(is_translatable left && is_translatable right) with
    | false -> fail "cannot be translated"
    | true ->
        let* res = prove_with_ctx (Binop (Eq, left, right)) in
        (match res with
        | `Valid ->
            let* _ = pop_pctxt in
            pure ()
        | _ -> fail "could not prove")
  in
  let is_prop =
    let rec could_be_prop t =
      match t with
      | True | False | Apply _ -> true
      | Binop ((Ge | Gt | Eq | Neq | Le | Lt), _, _) -> true
      | Implies (a, b) | Conj (a, b) | Disj (a, b) -> could_be_prop a && could_be_prop b
      | _ -> false
    in
    let* g = get_goal in
    match could_be_prop g with
    | false -> fail "not a prop"
    | true ->
        let* res = prove_with_ctx g in
        (match res with
        | `Valid ->
            let* _ = pop_pctxt in
            pure ()
        | _ -> fail "could not prove goal")
  in
  choices ~err:"failed to prove pure obligation"
    [both_values; is_prop; (* ens_ens; req_req;*) can_be_translated]

let induction =
 fun ?(vars = []) ~name kind x ->
  let open Tactic in
  let* assumptions = get_assumptions in
  let* x = get_constant x in
  let* vars = map_m get_constant vars in
  let assumptions = List.map snd (SMap.bindings assumptions) in
  let vars = Array.of_list vars in
  (* generate the body of the induction hypothesis *)
  let* g = get_goal in
  let ih_body = Induction.induction kind x vars assumptions g in
  (* and wrap it into a prop *)
  let ih_prop = Forall ih_body in
  add_assumption name ih_prop

let fresh =
  let* ctxt = get_rename_ctxt in
  let name, ctxt = Rename.Core.new_name "H" ctxt in
  let* () = put_rename_ctxt ctxt in
  pure name
