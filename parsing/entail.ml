open Hiptypes
open Pretty

let string_of_pi p = string_of_pi (ProversEx.normalize_pure p)

type 'a quantified = string list * 'a

let string_of_quantified to_s (vs, e) =
  match vs with
  | [] -> to_s e
  | _ :: _ -> Format.asprintf "ex %s. %s" (String.concat " " vs) (to_s e)

type instantiations = (string * string) list

let string_of_instantiations kvs =
  List.map (fun (k, v) -> Format.asprintf "%s := %s" k v) kvs
  |> String.concat ", " |> Format.asprintf "[%s]"

let rename_exists_spec sp = List.hd (Forward_rules.renamingexistientalVar [sp])

let rename_exists_lemma (lem : lemma) : lemma =
  {
    lem with
    l_left = rename_exists_spec lem.l_left;
    l_right = rename_exists_spec lem.l_right;
  }

exception Unification_failure

let match_lemma :
    string list ->
    lemma ->
    spec ->
    ((string * term) list * spec * normalisedStagedSpec) option =
 fun bound lem sp ->
  (* TODO normal stages are ignored for now *)
  let les, _ln = Pretty.normalise_spec lem.l_left in
  (* let lr = Pretty.normalise_spec lem.l_right in *)
  let ses, sn = Pretty.normalise_spec sp in
  (* collects bindings in acc, the prefix of s that is not matched, and goes until les is empty (fully matched). fails if ses becomes empty while les isn't *)
  let rec loop bound prefix acc les ses =
    match (les, ses) with
    | [], _ -> Some (acc, List.rev prefix, (ses, sn))
    | _ :: _, [] -> None
    | l1 :: les1, s1 :: ses1 ->
      (* matching is only done on constructors. other fields (state) probably have to be matched also but may require proof. not yet needed. also we probably shouldn't be invoking a prover for this, coq uses norm then syntactic equality to unify *)
      (* https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.apply *)
      let lc, la = l1.e_constr in
      let sc, sa = s1.e_constr in
      if (not (String.equal lc sc)) || not (List.compare_lengths la sa = 0) then
        (* try to find a match lower down *)
        (* TODO we should forget bindings when this happens *)
        loop bound
          (List.rev (normalisedStagedSpec2Spec ([s1], freshNormalStage))
          @ prefix)
          acc les1 ses1
      else (
        (* unify, get substitution, check it, then continue matching *)
        try
          let bs =
            List.map2 (fun a1 a2 -> (a1, a2)) (l1.e_ret :: la) (s1.e_ret :: sa)
            |> List.filter_map (function
                 | Var a, b when List.mem a bound -> Some (a, b)
                 | _ -> None)
          in
          (* alpha conversion: binders are equal up to renaming *)
          (* https://coq.inria.fr/refman/language/core/conversion.html *)
          (* let bs =
               match (l1.e_ret, s1.e_ret) with
               | Var vl, Var vs
                 when List.mem vl l1.e_evars && List.mem vs s1.e_evars ->
                 (vl, Var vs) :: bs
               | _ -> bs
             in *)
          (* TODO check if the bindings to the same name agree. if not, fail unification *)
          (* && match List.assoc_opt a acc with
                                  | None -> true
                                  | Some c when c = b -> false
                                  | Some _ -> raise Unification_failure *)
          (* matched, so don't add to the prefix *)
          let p, h = s1.e_post in
          loop bound
            (List.rev [Exists s1.e_evars; NormalReturn (p, h, UNIT)] @ prefix)
            (bs @ acc) les1 ses1
        with Unification_failure -> None)
  in
  loop bound [] [] les ses

let instantiate_res_existential lem =
  let _, (_, _, _, lret) = normalise_spec lem.l_left in
  let _, (_, _, _, rret) = normalise_spec lem.l_right in
  match (lret, rret) with
  | Var l, Var r ->
    {
      lem with
      l_right = Forward_rules.instantiateSpec [(r, Var l)] lem.l_right;
    }
  | _ -> lem

(** To use a lemma for rewriting, e.g. using l = (N1;N2 <: N3) to rewrite goal N0;N1;N2 to N0;N3, we match l against the goal by unifying segments, collecting bindings for universally-quantified variables, then replacing that portion of the goal once the match is complete. *)
let apply_lemma : lemma -> spec -> spec =
 fun lem sp ->
  let lem = rename_exists_lemma lem in
  let lem = instantiate_res_existential lem in
  match match_lemma lem.l_params lem sp with
  | None -> sp (* must be == *)
  | Some (bs, prefix, suffix) ->
    let inst_lem_rhs =
      List.map (Forward_rules.instantiateStages bs) lem.l_right
    in
    let inst_lem_rhs =
      (* add an extra equality between the return value and the variable it gets bound to outside *)
      let _, (_, _, _, ret1) = normalise_spec inst_lem_rhs in
      let _, (_, _, _, ret2) = normalise_spec sp in
      NormalReturn (Atomic (EQ, ret1, ret2), EmptyHeap, UNIT) :: inst_lem_rhs
    in
    let substituted : spec =
      prefix @ inst_lem_rhs @ normalisedStagedSpec2Spec suffix
    in
    substituted

let apply_one_lemma : lemma list -> spec -> spec * lemma option =
 fun lems sp ->
  List.fold_left
    (fun (sp, app) l ->
      match app with
      | Some _ -> (sp, app)
      | None ->
        let sp1 = apply_lemma l sp in
        if sp1 == sp then (sp, app) else (sp1, Some l))
    (sp, None) lems

let instantiate_pred : pred_def -> term list -> term -> pred_def =
 fun pred args ret ->
  (* the predicate should have one more arg than arguments given for the return value, which we'll substitute with the return term from the caller *)
  let params, ret_param = split_last pred.p_params in
  let bs = (ret_param, ret) :: List.map2 (fun a b -> (a, b)) params args in
  {
    pred with
    p_body =
      List.map
        (fun b -> List.map (Forward_rules.instantiateStages bs) b)
        pred.p_body;
  }

let conj xs =
  match xs with
  | [] -> True
  | x :: xs -> List.fold_right (fun c t -> And (c, t)) xs x

module Heap = struct
  open Res.Res
  (* let normalize_heap : kappa -> kappa * pi =
     fun h -> to_fixed_point_ptr_eq normaliseHeap h *)

  let normalize : state -> state =
   fun (p, h) ->
    let h = normaliseHeap h in
    (ProversEx.normalize_pure p, h)

  (** given a nonempty heap formula, splits it into a points-to expression and another heap formula *)
  let rec split_one : kappa -> ((string * term) * kappa) option =
   fun h ->
    match h with
    | EmptyHeap -> None
    | PointsTo (x, v) -> Some ((x, v), EmptyHeap)
    | SepConj (a, b) -> begin
      match split_one a with
      | None -> split_one b
      | Some (c, r) -> Some (c, SepConj (r, b))
    end

  (** like split_one, but searches for a particular points-to *)
  let rec split_find : string -> kappa -> (term * kappa) option =
   fun n h ->
    match h with
    | EmptyHeap -> None
    | PointsTo (x, v) when x = n -> Some (v, EmptyHeap)
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
            if String.equal x y then None
            else Some (Not (Atomic (EQ, Var x, Var y))))
          v2)
      v1
    |> conj

  let xpure : kappa -> pi =
   fun h ->
    let rec run h =
      match h with
      | EmptyHeap -> (True, [])
      | PointsTo (x, _t) -> (Atomic (GT, Var x, Num 0), [x])
      | SepConj (a, b) ->
        let a, v1 = run a in
        let b, v2 = run b in
        (And (a, And (b, pairwise_var_inequality v1 v2)), [])
    in
    let p, _vs = run h in
    p

  let rec check_qf :
      kappa -> string list -> state -> state -> (state * instantiations) pf =
   fun k vs ante conseq ->
    (* if debug then
       Format.printf "check_qf %s %s | %s |- %s@." (string_of_kappa k)
         (string_of_list Fun.id vs) (string_of_state ante)
         (string_of_state conseq); *)
    let a = normalize ante in
    let c = normalize conseq in
    match (a, c) with
    | (p1, h1), (p2, EmptyHeap) ->
      let left = And (xpure (SepConj (h1, k)), p1) in
      let valid = Provers.entails_exists left vs p2 in
      if valid then
        let pf =
          (* rule "xpure(%s * %s /\\ %s) => %s" (string_of_kappa h1)
             (string_of_kappa k) (string_of_pi p1) (string_of_pi p2) *)
          rule ~name:"ent-emp" "%s => %s" (string_of_pi left)
            (string_of_quantified string_of_pi (vs, p2))
        in
        Ok (pf, ((p1, h1), []))
      else
        Error
          (rule ~name:"ent-emp" ~success:false "%s => %s" (string_of_pi left)
             (string_of_quantified string_of_pi (vs, p2)))
    | (p1, h1), (p2, h2) -> begin
      (* we know h2 is non-empty *)
      match split_one h2 with
      | Some ((x, v), h2') when List.mem x vs ->
        (* x is bound and could potentially be instantiated with anything on the right side, so try everything *)
        let r1 =
          any ~name:"ent-match-any"
            ~to_s:(fun ((lx, lv), (rx, rv)) ->
              Format.asprintf "%s->%s and ex %s. %s->%s" lx (string_of_term lv)
                rx rx (string_of_term rv))
            (list_of_heap h1 |> List.map (fun a -> (a, (x, v))))
            (fun ((x1, v1), _) ->
              let v2, h1' = split_find x1 h1 |> Option.get in
              (* matching ptr values are added as an eq to the right side, since we don't have a term := term substitution function *)
              let* pf, (st, inst) =
                check_qf
                  (SepConj (k, PointsTo (x1, v1)))
                  (List.filter (fun v1 -> not (String.equal v1 x)) vs)
                  ( And
                      (p1, And (Atomic (EQ, Var x1, Var x), Atomic (EQ, v, v1))),
                    h1' )
                  (And (Atomic (EQ, v, v2), p2), h2')
              in
              Ok (pf, (st, (x, x1) :: inst)))
        in
        begin
          match r1 with
          | Error s ->
            Error
              (rule ~children:[s] ~name:"ent-match" ~success:false
                 "ex %s. %s->%s" x x (string_of_term v))
          | Ok (pf, res) ->
            Ok
              ( rule ~children:[pf] ~name:"ent-match" "ex %s. %s->%s" x x
                  (string_of_term v),
                res )
        end
      | Some ((x, v), h2') -> begin
        (* x is free. match against h1 exactly *)
        match split_find x h1 with
        | Some (v1, h1') -> begin
          match
            check_qf
              (SepConj (k, PointsTo (x, v)))
              vs
              (And (p1, Atomic (EQ, v, v1)), h1')
              (p2, h2')
          with
          | Error s ->
            Error
              (rule ~children:[s] ~name:"ent-match" ~success:false
                 "%s->%s and %s->%s" x (string_of_term v) x (string_of_term v1))
          | Ok (pf, res) ->
            Ok
              ( rule ~children:[pf] ~name:"ent-match" "%s->%s and %s->%s" x
                  (string_of_term v) x (string_of_term v1),
                res )
        end
        | None ->
          Error
            (rule ~name:"ent-match" ~success:false
               "could not match %s->%s on RHS" x (string_of_term v))
        (* failwith
           (Format.asprintf "Heap.check: could not match %s->%s on RHS" x
              (string_of_term v)) *)
      end
      | None -> failwith (Format.asprintf "could not split LHS, bug?")
    end

  let check_exists :
      state quantified -> state quantified -> (state * instantiations) pf =
   fun (avs, ante) (cvs, conseq) ->
    (* if debug then
       Format.printf "check_exists (%s, %s) |- (%s, %s)@."
         (string_of_list Fun.id avs)
         (string_of_state ante)
         (string_of_list Fun.id cvs)
         (string_of_state conseq); *)
    (* replace left side with fresh variables *)
    let left =
      let p, h = ante in
      let fresh =
        List.map (fun a -> (a, Var (verifier_getAfreeVar ~from:a ()))) avs
      in
      ( Forward_rules.instantiatePure fresh p,
        Forward_rules.instantiateHeap fresh h )
    in
    let right, vs =
      (* do the same for the right side, but track them *)
      if false then
        (* TODO disable for now. when enabled, maintain a mapping so anything keeping track of the variables higher up can also rename... *)
        let p, h = conseq in
        let fresh_names =
          List.map (fun a -> (a, verifier_getAfreeVar ~from:a ())) cvs
        in
        let fresh_vars = List.map (fun (a, b) -> (a, Var b)) fresh_names in
        ( ( Forward_rules.instantiatePure fresh_vars p,
            Forward_rules.instantiateHeap fresh_vars h ),
          List.map snd fresh_names )
      else (conseq, cvs)
    in
    check_qf EmptyHeap vs left right

  let entails :
      state quantified -> state quantified -> (state * instantiations) pf =
   fun s1 s2 -> check_exists s1 s2

  let%expect_test "heap_entail" =
    verifier_counter_reset ();
    Pretty.colours := `None;
    let test l r =
      let res =
        match entails l r with
        | Error pf -> Format.asprintf "FAIL\n%s" (string_of_proof pf)
        | Ok (pf, (residue, inst)) ->
          Format.asprintf "%s %s\n%s" (string_of_state residue)
            (string_of_instantiations inst)
            (string_of_proof pf)
      in
      Format.printf "%s |- %s ==> %s@."
        (string_of_quantified string_of_state l)
        (string_of_quantified string_of_state r)
        res
    in

    test ([], (True, PointsTo ("x", Num 1))) ([], (True, PointsTo ("y", Num 2)));
    test ([], (True, PointsTo ("x", Num 1))) ([], (True, PointsTo ("x", Num 1)));
    test
      ([], (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2))))
      ([], (True, PointsTo ("x", Num 1)));
    test
      ([], (True, PointsTo ("x", Num 1)))
      ([], (True, PointsTo ("x", Var "a")));
    test
      ([], (True, PointsTo ("x", Var "b")))
      ([], (True, PointsTo ("x", Var "a")));
    (* quantified *)
    test
      ([], (True, SepConj (PointsTo ("y", Var "c"), PointsTo ("x", Var "b"))))
      (["x"], (True, PointsTo ("x", Var "a")));
    test
      ([], (True, SepConj (PointsTo ("y", Var "3"), PointsTo ("x", Var "2"))))
      (["x"], (True, PointsTo ("x", Var "1+1")));
    [%expect
      {|
      x->1 |- y->2 ==> FAIL
      │[ent-match] FAIL could not match y->2 on RHS

      x->1 |- x->1 ==> 1=1 []
      │[ent-match] x->1 and x->1
      │└── [ent-emp] x>0/\1=1 => T

      x->1*y->2 |- x->1 ==> y->2 /\ 1=1 []
      │[ent-match] x->1 and x->1
      │└── [ent-emp] y>0/\x>0/\1=1 => T

      x->1 |- x->a ==> a=1 []
      │[ent-match] x->a and x->1
      │└── [ent-emp] x>0/\a=1 => T

      x->b |- x->a ==> a=b []
      │[ent-match] x->a and x->b
      │└── [ent-emp] x>0/\a=b => T

      y->c*x->b |- ex x. x->a ==> x->b /\ y=x/\a=c [x := y]
      │[ent-match] ex x. x->a
      │└── [ent-match-any] y->c and ex x. x->a
      │    └── [ent-emp] x>0/\y>0/\y=x/\a=c => a=c

      y->3*x->2 |- ex x. x->1+1 ==> x->2 /\ y=x/\1+1=3 [x := y]
      │[ent-match] ex x. x->1+1
      │└── [ent-match-any] y->3 and ex x. x->1+1
      │    └── [ent-emp] x>0/\y>0/\y=x/\1+1=3 => 1+1=3 |}]
end

let check_staged_entail : spec -> spec -> spec option =
 fun n1 n2 ->
  let norm = normalise_spec (n1 @ n2) in
  Some (normalisedStagedSpec2Spec norm)

let instantiate_state bindings (p, h) =
  ( Forward_rules.instantiatePure bindings p,
    Forward_rules.instantiateHeap bindings h )

let instantiate_existentials_effect_stage bindings =
  let names = List.map fst bindings in
  fun eff ->
    {
      eff with
      e_evars = List.filter (fun v -> not (List.mem v names)) eff.e_evars;
      e_pre = instantiate_state bindings eff.e_pre;
      e_post = instantiate_state bindings eff.e_post;
      e_constr =
        ( fst eff.e_constr,
          List.map (Forward_rules.instantiateTerms bindings) (snd eff.e_constr)
        );
      e_ret = Forward_rules.instantiateTerms bindings eff.e_ret;
    }

(** actually instantiates existentials, vs what the forward rules version does *)
let instantiate_existentials :
    (string * term) list -> normalisedStagedSpec -> normalisedStagedSpec =
 fun bindings (efs, ns) ->
  let names = List.map fst bindings in
  let efs1 = List.map (instantiate_existentials_effect_stage bindings) efs in
  let ns1 =
    let vs, pre, post, ret = ns in
    ( List.filter (fun v -> not (List.mem v names)) vs,
      instantiate_state bindings pre,
      instantiate_state bindings post,
      Forward_rules.instantiateTerms bindings ret )
  in
  (efs1, ns1)

let freshen_existentials vs state =
  let vars_fresh =
    List.map (fun v -> (v, Var (verifier_getAfreeVar ~from:v ()))) vs
  in
  (vars_fresh, instantiate_state vars_fresh state)

(* let es1, (_, pre, post, ret) = instantiate_existentials vars_fresh norm in
   ( List.map (fun (_, pre, post, eff, ret) -> ([], pre, post, eff, ret)) es1,
     ([], pre, post, ret) ) *)

(* let rec check_staged_subsumption_ :
      normalisedStagedSpec -> normalisedStagedSpec -> state pf =
   fun s1 s2 ->
    (* recurse down both lists in parallel *)
    match (s1, s2) with
    | (es1 :: es1r, ns1), (es2 :: es2r, ns2) -> begin
      let {
        e_evars = vs1;
        e_pre = p1, h1;
        e_post = qp1, qh1;
        e_constr = nm1, _a1;
        e_ret = r1;
        _;
      } =
        es1
      in
      let {
        e_evars = vs2;
        e_pre = p2, h2;
        e_post = qp2, qh2;
        e_constr = nm2, _a2;
        e_ret = r2;
        _;
      } =
        es2
      in
      (* bound variables continue to be bound in the rest of the expression *)
      (* TODO propagate any constraints we discover on them *)
      (* let vs1 = List.sort_uniq String.compare (vs1 @ vs1') in *)
      (* let vs1 = [] in *)
      (* TODO this is not very efficient *)
      (* let vs2 = List.sort_uniq String.compare (vs2 @ vs2') in *)
      let sub, pre = freshen_existentials vs2 (p2, h2) in
      (* let r2 = Forward_rules.instantiateTerms sub r2 in *)
      let es2r = List.map (instantiate_existentials_effect_stage sub) es2r in

      (* contravariance of preconditions *)
      let* pf1, ((pr, hr), inst1) = Heap.entails ([], pre) (vs1, (p1, h1)) in

      let sub, post = freshen_existentials vs1 (qp1, qh1) in
      (* let ns1 =  *)
      (* let es1r = List.map (instantiate_existentials_effect_stage sub) es1r in *)
      let es1r, ns1 = instantiate_existentials sub (es1r, ns1) in
      let r1 = Forward_rules.instantiateTerms sub r1 in

      let res_v = verifier_getAfreeVar ~from:"res" () in
      (* covariance of postconditions *)
      let* pf2, ((_pr, _hr), inst2) =
        let qp1, qh1 = post in
        Heap.entails
          ( [],
            (And (qp1, And (pr, Atomic (EQ, r1, Var res_v))), SepConj (qh1, hr))
          )
          (vs2, (And (qp2, Atomic (EQ, r2, Var res_v)), qh2))
      in
      (* compare effect names *)
      let* _ =
        if String.equal nm1 nm2 then Ok ()
        else Error (rule ~name:"name-equal" "uh oh")
      in
      (* TODO prove return values are the same as part of the heap entailment? *)
      (* unify effect params and return value *)
      (* let unify =
           List.fold_right
             (fun (a, b) t -> And (t, Atomic (EQ, a, b)))
             (List.map2 (fun a b -> (a, b)) a1 a2)
             (Atomic (EQ, r1, r2))
         in *)
      let inst =
        let ret =
          match (r2, r1) with
          | Var s2, Var s1 when List.mem s2 vs2 ->
            (* both r1 and r2 are effects so their return terms should be variables. the real check is whether r2 is quantified *)
            [(s2, s1)]
          | _ -> []
        in
        ret @ inst1 @ inst2
      in
      (* TODO check if vars are removed from the new spec *)
      (* substitute the instantiated variables away, also in the state we are maintaining *)
      (* let es2', ns2 = Forward_rules.instantiateExistientalVar (es2', ns2) inst in *)
      let es2r, ns2 =
        instantiate_existentials
          (List.map (fun (a, b) -> (a, Var b)) inst)
          (es2r, ns2)
      in
      let _vs2 =
        List.filter (fun v -> not (List.mem v (List.map fst inst))) vs2
      in
      let* pf, res = check_staged_subsumption_ (es1r, ns1) (es2r, ns2) in
      Ok
        ( rule ~children:[pf1; pf2; pf] ~name:"subsumption-stage" "%s |= %s"
            (string_of_spec (normalisedStagedSpec2Spec s1))
            (string_of_spec (normalisedStagedSpec2Spec s2)),
          res )
    end
    | ([], ns1), ([], ns2) ->
      (* base case: check the normal stage at the end *)
      let (vs1, (p1, h1), (qp1, qh1), r1), (vs2, (p2, h2), (qp2, qh2), r2) =
        (ns1, ns2)
      in
      (* let vs1 = List.sort_uniq String.compare (vs1 @ vs1') in *)
      (* let vs2 = List.sort_uniq String.compare (vs2 @ vs2') in *)
      (* contravariance *)
      let* pf1, ((pr, hr), _inst1) =
        Heap.entails (vs2, (p2, h2)) (vs1, (p1, h1))
      in
      let res_v = verifier_getAfreeVar ~from:"res" () in
      (* covariance *)
      let* pf2, ((pr, hr), _inst2) =
        Heap.entails
          ( vs1,
            (And (And (qp1, Atomic (EQ, Var res_v, r1)), pr), SepConj (qh1, hr))
          )
          (vs2, (And (qp2, Atomic (EQ, Var res_v, r2)), qh2))
      in
      (* unify return value *)
      let pure = Atomic (EQ, r1, r2) in
      Ok
        ( rule ~children:[pf1; pf2] ~name:"subsumption-base" "%s |= %s"
            (string_of_spec (normalStage2Spec ns1))
            (string_of_spec (normalStage2Spec ns2)),
          (And (pr, pure), hr) )
    | _ -> Error (rule ~name:"subsumption-stage" ~success:false "unequal length") *)

let ( let@ ) f x = f x

open Res.Option

(** Given two heap formulae, matches points-to predicates
  may backtrack if the locations are quantified.
  returns (by invoking the continuation) when matching is complete (when right is empty).

  id: human-readable name
  vs: quantified variables
  k: continuation
*)
let rec check_qf2 :
    string ->
    string list ->
    state ->
    state ->
    (pi * pi -> 'a option) ->
    'a option =
 fun id vs ante conseq k ->
  (* TODO ptr equalities? *)
  let a = Heap.normalize ante in
  let c = Heap.normalize conseq in
  debug "%s |- %s@." (string_of_state ante) (string_of_state conseq);
  match (a, c) with
  | (p1, h1), (p2, EmptyHeap) ->
    let left = And (Heap.xpure h1, p1) in
    k (left, p2)
  | (p1, h1), (p2, h2) -> begin
    (* we know h2 is non-empty *)
    match Heap.split_one h2 with
    | Some ((x, v), h2') when List.mem x vs ->
      let left_heap = list_of_heap h1 in
      (match left_heap with
      | [] -> None
      | _ :: _ ->
        (* x is bound and could potentially be instantiated with anything on the right side, so try everything *)
        let r1 =
          any
            ~to_s:(fun (a, _) -> string_of_pair Fun.id string_of_term a)
            ~name:"ent-match-any"
            (left_heap |> List.map (fun a -> (a, (x, v))))
            (fun ((x1, v1), _) ->
              let _v2, h1' = Heap.split_find x1 h1 |> Option.get in
              (* ptr equality *)
              let _ptr_eq = Atomic (EQ, Var x1, Var x) in
              (* fresh vars for v and v1 so unifier can be on the left *)
              let fl = verifier_getAfreeVar ~from:(x ^ "v_" ^ id) () in
              let fr = verifier_getAfreeVar ~from:(x1 ^ "v_" ^ id) () in
              let _fleq = Atomic (EQ, Var fl, v) in
              let _freq = Atomic (EQ, Var fr, v1) in
              let _unifier = Atomic (EQ, Var fl, Var fr) in
              let triv = Atomic (EQ, v, v1) in
              (* matching ptr values are added as an eq to the right side, since we don't have a term := term substitution function *)
              check_qf2 id vs (conj [p1], h1') (conj [p2; triv], h2') k)
        in
        r1)
    | Some ((x, v), h2') -> begin
      (* x is free. match against h1 exactly *)
      match Heap.split_find x h1 with
      | Some (v1, h1') -> begin
        check_qf2 (* (SepConj (k, PointsTo (x, v))) *) id vs
          (conj [p1], h1')
          (conj [p2; And (p1, Atomic (EQ, v, v1))], h2')
          k
        (* with
           | Error s ->
             Error
               (rule ~children:[s] ~name:"ent-match" ~success:false
                  "%s->%s and %s->%s" x (string_of_term v) x (string_of_term v1))
           | Ok (pf, res) ->
             Ok
               ( rule ~children:[pf] ~name:"ent-match" "%s->%s and %s->%s" x
                   (string_of_term v) x (string_of_term v1),
                 res ) *)
      end
      | None -> None
      (* failwith
         (Format.asprintf "Heap.check: could not match %s->%s on RHS" x
            (string_of_term v)) *)
    end
    | None -> failwith (Format.asprintf "could not split LHS, bug?")
  end

let with_pure pi ((p, h) : state) : state = (conj [p; pi], h)

let rec unfold_predicate_aux pred prefix already (s : spec) : disj_spec =
  match s with
  | [] -> List.map List.rev prefix
  | HigherOrder (_p, _h, (name, args), ret) :: s1
    when String.equal name pred.p_name && not (List.mem name already) ->
    info ~title:(Format.asprintf "unfolding: %s" name) "@.";
    let pred1 = instantiate_pred pred args ret in
    let pref : disj_spec =
      List.concat_map
        (fun p -> List.map (fun b -> List.rev b @ p) pred1.p_body)
        prefix
    in
    unfold_predicate_aux pred pref already s1
  | c :: s1 ->
    let pref = List.map (fun p -> c :: p) prefix in
    unfold_predicate_aux pred pref already s1

(** f;a;e \/ b and a == c \/ d
  => f;(c \/ d);e \/ b
  => f;c;e \/ f;d;e \/ b *)
let unfold_predicate : pred_def -> disj_spec -> disj_spec =
 fun pred ds ->
  List.concat_map (fun s -> unfold_predicate_aux pred [[]] [] s) ds

let unfold_predicate_spec : pred_def -> spec -> disj_spec =
 fun pred sp -> unfold_predicate_aux pred [[]] [] sp

let unfold_predicate_norm :
    pred_def -> normalisedStagedSpec -> normalisedStagedSpec list =
 fun pred sp ->
  List.map normalise_spec
    (unfold_predicate_spec pred (normalisedStagedSpec2Spec sp))

(** proof context *)
type pctx = {
  lems : lemma list;
  preds : pred_def SMap.t;
  (* all quantified variables in this formula *)
  q_vars : string list;
  (* predicates which have been unfolded, used as an approximation of progress (in the cyclic proof sense) *)
  unfolded : string list;
  (* lemmas applied *)
  applied : string list;
}

let default_pctx lems preds q_vars =
  { lems; preds; q_vars; unfolded = []; applied = [] }

(** Recurses down a normalised staged spec, matching stages,
   translating away heap predicates to build a pure formula,
   and proving subsumption of each pair of stages.
   Residue from previous stages is assumed.

   Matching of quantified locations may cause backtracking.
   Other quantifiers are left to z3 to instantiate.
   
   i: index of stage
   all_vars: all quantified variables
*)
let rec check_staged_subsumption_aux :
    pctx ->
    int ->
    pi ->
    normalisedStagedSpec ->
    normalisedStagedSpec ->
    unit option =
 fun ctx i assump s1 s2 ->
  info ~title:"subsumption" "%s\n<:\n%s\n@."
    (string_of_normalisedStagedSpec s1)
    (string_of_normalisedStagedSpec s2);
  match (s1, s2) with
  | (es1 :: es1r, ns1), (es2 :: es2r, ns2) ->
    (* fail fast by doing easy checks first *)
    let c1, a1 = es1.e_constr in
    let c2, a2 = es2.e_constr in
    (match String.equal c1 c2 with
    | false ->
      let@ _ =
        try_other_measures ctx s1 s2 None (Some c2) i assump |> or_else
      in
      info "FAIL, constr %s != %s@." c1 c2;
      fail
      (* try to unfold the right side, then the left *)
      (* (match List.find_opt (fun p -> String.equal c2 p.p_name) ctx.preds with
         | Some def when not (List.mem c2 ctx.unfolded) ->
           let unf = unfold_predicate_norm def s2 in
           let@ s2_1 = any ~name:"?" ~to_s:string_of_normalisedStagedSpec unf in
           check_staged_subsumption_aux
             { ctx with unfolded = c2 :: ctx.unfolded }
             i assump s1 s2_1
         | _ ->
           (match List.find_opt (fun p -> String.equal c1 p.p_name) ctx.preds with
           | Some def when not (List.mem c1 ctx.unfolded) ->
             let unf = unfold_predicate_norm def s1 in
             let@ s1_1 = all ~to_s:string_of_normalisedStagedSpec unf in
             check_staged_subsumption_aux
               { ctx with unfolded = c1 :: ctx.unfolded }
               i assump s1_1 s2
           | _ ->
             (* try to apply a lemma *)
             let eligible =
               ctx.lems
               |> List.filter (fun l -> List.mem l.l_name ctx.unfolded)
               |> List.filter (fun l -> not (List.mem l.l_name ctx.applied))
             in
             let s1_1, applied =
               apply_one_lemma eligible (normalisedStagedSpec2Spec s1)
             in
             (match applied with
             | Some app ->
               check_staged_subsumption_aux
                 { ctx with applied = app :: ctx.unfolded }
                 i assump (normalise_spec s1_1) s2
             | None ->
               (* no predicates to try unfolding *)
               info "FAIL, constr %s != %s@." c1 c2;
               fail))) *)
    | true ->
      let* _ =
        let l1 = List.length a1 in
        let l2 = List.length a2 in
        let r = l1 = l2 in
        if not r then (
          info "FAIL, arg length %s (%d) != %s (%d)@."
            (string_of_list string_of_term a1)
            l1
            (string_of_list string_of_term a2)
            l2;
          fail)
        else ok
      in
      let* residue =
        let arg_eqs = conj (List.map2 (fun x y -> Atomic (EQ, x, y)) a1 a2) in
        stage_subsumes ctx
          (Format.asprintf "Eff %d" i)
          assump
          (es1.e_evars, (es1.e_pre, es1.e_post, es1.e_ret))
          (es2.e_evars, (es2.e_pre, with_pure arg_eqs es2.e_post, es2.e_ret))
      in
      check_staged_subsumption_aux ctx (i + 1)
        (conj [assump; residue])
        (es1r, ns1) (es2r, ns2))
  | ([], ns1), ([], ns2) ->
    (* base case: check the normal stage at the end *)
    let (vs1, (p1, h1), (qp1, qh1), r1), (vs2, (p2, h2), (qp2, qh2), r2) =
      (ns1, ns2)
    in
    let* _residue =
      stage_subsumes ctx "Norm" assump
        (vs1, ((p1, h1), (qp1, qh1), r1))
        (vs2, ((p2, h2), (qp2, qh2), r2))
    in
    ok
  | ([], _), (es2 :: _, _) ->
    let c2, _ = es2.e_constr in
    let@ _ = try_other_measures ctx s1 s2 None (Some c2) i assump |> or_else in
    (* try to unfold predicates *)
    (* (match List.find_opt (fun p -> String.equal c2 p.p_name) ctx.preds with
       | Some def when not (List.mem c2 ctx.unfolded) ->
         let unf = unfold_predicate_norm def s2 in
         let@ s2_1 = any ~name:"?" ~to_s:string_of_normalisedStagedSpec unf in
         check_staged_subsumption_aux
           { ctx with unfolded = c2 :: ctx.unfolded }
           i assump s1 s2_1
       | _ -> *)
    info "FAIL, ante is shorter\n%s\n<:\n%s\n@."
      (string_of_normalisedStagedSpec s1)
      (string_of_normalisedStagedSpec s2);
    fail
  | (es1 :: _, _), ([], _) ->
    (* try to unfold predicates *)
    let c1, _ = es1.e_constr in
    let@ _ = try_other_measures ctx s1 s2 (Some c1) None i assump |> or_else in
    (* match List.find_opt (fun p -> String.equal c1 p.p_name) ctx.preds with
       | Some def when not (List.mem c1 ctx.unfolded) ->
         let unf = unfold_predicate_norm def s1 in
         let@ s1_1 = all ~to_s:string_of_normalisedStagedSpec unf in
         check_staged_subsumption_aux
           { ctx with unfolded = c1 :: ctx.unfolded }
           i assump s1 s1_1
       | _ -> *)
    info "FAIL, conseq is shorter\n%s\n<:\n%s\n@."
      (string_of_normalisedStagedSpec s1)
      (string_of_normalisedStagedSpec s2);
    fail

and try_other_measures :
    pctx ->
    normalisedStagedSpec ->
    normalisedStagedSpec ->
    string option ->
    string option ->
    int ->
    pi ->
    unit option =
 fun ctx s1 s2 c1 c2 i assump ->
  (* first try to unfold on the right *)
  match
    let* c2 = c2 in
    let+ res = SMap.find_opt c2 ctx.preds in
    (c2, res)
  with
  | Some (c2, def) when not (List.mem c2 ctx.unfolded) ->
    let unf = unfold_predicate_norm def s2 in
    if List.length unf > 1 then
      info ~title:"after unfolding (right)" "%s\n<:\n%s\n@."
        (string_of_normalisedStagedSpec s1)
        (string_of_disj_spec (List.map normalisedStagedSpec2Spec unf));
    let@ s2_1 = any ~name:"?" ~to_s:string_of_normalisedStagedSpec unf in
    check_staged_subsumption_aux
      { ctx with unfolded = c2 :: ctx.unfolded }
      i assump s1 s2_1
  | _ ->
    (* if that fails, unfold on the left *)
    (match
       let* c1 = c1 in
       let+ res = SMap.find_opt c1 ctx.preds in
       (c1, res)
     with
    | Some (c1, def) when not (List.mem c1 ctx.unfolded) ->
      let unf = unfold_predicate_norm def s1 in
      if List.length unf > 1 then
        info ~title:"after unfolding (left)" "%s\n<:\n%s\n@."
          (string_of_disj_spec (List.map normalisedStagedSpec2Spec unf))
          (string_of_normalisedStagedSpec s2);
      let@ s1_1 = all ~to_s:string_of_normalisedStagedSpec unf in
      check_staged_subsumption_aux
        { ctx with unfolded = c1 :: ctx.unfolded }
        i assump s1_1 s2
    | _ ->
      (* if that fails, try to apply a lemma *)
      let eligible =
        ctx.lems
        (* |> List.filter (fun l -> List.mem l.l_name ctx.unfolded) *)
        |> List.filter (fun l -> not (List.mem l.l_name ctx.applied))
      in
      let s1_1, applied =
        apply_one_lemma eligible (normalisedStagedSpec2Spec s1)
      in
      applied
      |> Option.iter (fun l ->
             info
               ~title:(Format.asprintf "applied: %s" l.l_name)
               "%s\n\n%s\n<:\n%s\n@." (string_of_lemma l) (string_of_spec s1_1)
               (string_of_normalisedStagedSpec s2));
      (match applied with
      | Some app ->
        check_staged_subsumption_aux
          { ctx with applied = app.l_name :: ctx.unfolded }
          i assump (normalise_spec s1_1) s2
      | None ->
        (* no predicates to try unfolding *)
        info "FAIL, constr %s != %s@."
          (string_of_option Fun.id c1)
          (string_of_option Fun.id c2);
        fail))

and stage_subsumes :
    pctx ->
    string ->
    pi ->
    (state * state * term) quantified ->
    (state * state * term) quantified ->
    pi option =
 fun ctx what assump s1 s2 ->
  let vs1, (pre1, post1, ret1) = s1 in
  let vs2, (pre2, post2, ret2) = s2 in
  (* TODO replace uses of all_vars. this is for us to know if locations on the rhs are quantified. a smaller set of vars is possible *)
  info "%s %s * (%sreq %s; ens %s) <: (%sreq %s; ens %s)@."
    (Pretty.yellow (Format.asprintf "(%s)" what))
    (string_of_pi assump)
    (string_of_existentials vs1)
    (string_of_state pre1) (string_of_state post1)
    (string_of_existentials vs2)
    (string_of_state pre1) (string_of_state post2);
  (* contravariance *)
  let@ pre_l, pre_r = check_qf2 "pren" ctx.q_vars pre2 pre1 in
  let* assump =
    let left = conj [assump; pre_l] in
    let right = pre_r in
    let pre_res = Provers.entails_exists left vs1 right in
    info "%s %s => %s%s ==> %s@."
      (Pretty.yellow (Format.asprintf "(%s pre)" what))
      (string_of_pi left)
      (string_of_existentials vs1)
      (string_of_pi right) (string_of_res pre_res);
    of_bool (conj [pre_l; pre_r; assump]) pre_res
  in
  (* covariance *)
  let new_univ = SSet.union (used_vars_pi pre_l) (used_vars_pi pre_r) in
  let vs22 = List.filter (fun v -> not (SSet.mem v new_univ)) vs2 in
  (* let res_v = verifier_getAfreeVar ~from:"res" () in *)
  let@ post_l, post_r = check_qf2 "postn" ctx.q_vars post1 post2 in
  let* residue =
    (* Atomic (EQ, Var res_v, ret1) *)
    (* Atomic (EQ, Var res_v, ret2) *)
    (* don't use fresh variable for the ret value so it carries forward in the residue *)
    let left = conj [assump; post_l] in
    let right = conj [post_r; Atomic (EQ, ret1, ret2)] in
    let post_res = Provers.entails_exists left vs22 right in
    info "%s %s => %s%s ==> %s@."
      (Pretty.yellow (Format.asprintf "(%s post)" what))
      (string_of_pi left)
      (string_of_existentials vs22)
      (string_of_pi right) (string_of_res post_res);
    of_bool (conj [right; assump]) post_res
  in
  pure residue

let extract_binders spec =
  let binders, rest =
    List.partition_map (function Exists vs -> Left vs | s -> Right s) spec
  in
  (List.concat binders, rest)

let rec apply_tactics ts lems preds (ds1 : disj_spec) (ds2 : disj_spec) =
  List.fold_left
    (fun t c ->
      let ds1, ds2 = t in
      let r =
        match c with
        | Unfold_right ->
          info "%s %s@."
            (Pretty.yellow "unfold right")
            ((string_of_smap string_of_pred) preds);
          let ds2 = SMap.fold (fun _n -> unfold_predicate) preds ds2 in
          (ds1, ds2)
        | Unfold_left ->
          info "%s %s@."
            (Pretty.yellow "unfold left")
            (string_of_smap string_of_pred preds);
          let ds1 = SMap.fold (fun _n -> unfold_predicate) preds ds1 in
          (ds1, ds2)
        | Case (i, ta) ->
          (* case works on the left only *)
          info "%s@." (Pretty.yellow (Format.sprintf "case %d" i));
          let ds, _ = apply_tactics [ta] lems preds [List.nth ds1 i] ds2 in
          (* unfolding (or otherwise adding disjuncts) inside case will break use of hd *)
          let ds11 = replace_nth i (List.hd ds) ds1 in
          (ds11, ds2)
        | Apply l ->
          (* apply works on the left only *)
          info "%s@." (Pretty.yellow (Format.sprintf "apply %s" l));
          ( List.map
              (List.fold_right apply_lemma
                 (List.filter (fun le -> String.equal le.l_name l) lems))
              ds1,
            ds2 )
      in
      info "%s\n<:\n%s\n@."
        (string_of_disj_spec (fst r))
        (string_of_disj_spec (snd r));
      r)
    (ds1, ds2) ts

let check_staged_subsumption :
    string list -> lemma list -> pred_def SMap.t -> spec -> spec -> unit option
    =
 fun params lems preds n1 n2 ->
  let ((es1, ns1) as nn1) = normalise_spec n1 in
  let ((es2, ns2) as nn2) = normalise_spec n2 in
  let q_vars =
    Forward_rules.getExistientalVar (es1, ns1)
    @ Forward_rules.getExistientalVar (es2, ns2)
  in
  let ih_lemma =
    {
      l_name = "IH";
      l_params = params;
      l_left = normalisedStagedSpec2Spec nn1;
      l_right = normalisedStagedSpec2Spec nn2;
    }
  in
  let ctx = default_pctx (ih_lemma :: lems) preds q_vars in
  check_staged_subsumption_aux ctx 0 True (es1, ns1) (es2, ns2)

(**
  Subsumption between disjunctive specs.
  S1 \/ S2 |= S3 \/ S4
*)
let check_staged_subsumption_disj :
    string list ->
    tactic list ->
    lemma list ->
    pred_def SMap.t ->
    disj_spec ->
    disj_spec ->
    bool =
 fun params _ts lems preds ds1 ds2 ->
  info ~title:"before tactics" "%s\n<:\n%s\n@." (string_of_disj_spec ds1)
    (string_of_disj_spec ds2);
  (* let ds1, ds2 = apply_tactics ts lems preds ds1 ds2 in *)
  (let@ s1 = all ~to_s:string_of_spec ds1 in
   let@ s2 = any ~name:"subsumes-disj-rhs-any" ~to_s:string_of_spec ds2 in
   check_staged_subsumption params lems preds s1 s2)
  |> succeeded

let derive_predicate meth disj =
  let norm = List.map normalise_spec disj in
  (* change the last norm stage so it uses res and has an equality constraint *)
  let new_spec =
    List.map
      (fun (effs, (vs, pre, (p, h), r)) ->
        (effs, (vs, pre, (conj [p; Atomic (EQ, Var "res", r)], h), Var "res")))
      norm
    |> List.map normalisedStagedSpec2Spec
  in
  {
    p_name = meth.m_name;
    p_params = meth.m_params @ ["res"];
    p_body = new_spec;
  }

let%expect_test _ =
  let left =
    [
      [
        Exists ["q"; "q1"];
        Require (True, PointsTo ("x", Var "q"));
        NormalReturn
          (Atomic (GT, Var "q1", Var "q"), PointsTo ("x", Var "q1"), Num 2);
      ];
    ]
  in
  let right =
    [
      [
        Exists ["p"];
        Require (True, PointsTo ("x", Var "p"));
        NormalReturn (True, PointsTo ("x", Plus (Var "p", Num 1)), Num 2);
      ];
    ]
  in
  Format.printf "%b@."
    (check_staged_subsumption_disj [] [] [] SMap.empty left right);
  Format.printf "%b@."
    (check_staged_subsumption_disj [] [] [] SMap.empty right left);
  [%expect {|
    false
    true
          |}]
