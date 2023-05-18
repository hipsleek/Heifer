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

let instantiate_lemma : lemma -> term list -> term -> lemma =
 fun lem args ret ->
  let params, ret_param =
    match lem.l_left with
    | HigherOrder (_, _, (_, params), Var ret_param) ->
      ( List.map (function Var s -> s | _ -> failwith "not a var") params,
        [(ret_param, ret)] )
    | _ -> failwith "unknown kind of lemma"
  in
  let bs = ret_param @ List.map2 (fun a b -> (a, b)) params args in
  {
    lem with
    l_left = (Forward_rules.instantiateStages bs) lem.l_left;
    l_right = List.map (Forward_rules.instantiateStages bs) lem.l_right;
  }

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

(** single application *)
let apply_lemma : lemma -> spec -> spec =
 fun lem sp ->
  let tr s =
    (* for now, lemmas are only applied from left to right, and the left side must be a predicate *)
    match (s, lem.l_left) with
    | Exists _, _ | Require (_, _), _ | NormalReturn _, _ | RaisingEff _, _ ->
      [s]
    | HigherOrder (_p, _h, (name, args), r), HigherOrder (_, _, (lem_name, _), _)
      when String.equal name lem_name ->
      (instantiate_lemma lem args r).l_right
    | HigherOrder _, _ -> [s]
  in
  List.concat_map tr sp

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
      match split_one a with None -> split_one b | Some r -> Some r
    end

  (** like split_one, but searches for a particular points-to *)
  let rec split_find : string -> kappa -> (term * kappa) option =
   fun n h ->
    match h with
    | EmptyHeap -> None
    | PointsTo (x, v) when x = n -> Some (v, EmptyHeap)
    | PointsTo _ -> None
    | SepConj (a, b) -> begin
      match split_find n a with None -> split_find n b | Some r -> Some r
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

      x->1*y->2 |- x->1 ==> 1=1 []
      │[ent-match] x->1 and x->1
      │└── [ent-emp] x>0/\1=1 => T

      x->1 |- x->a ==> a=1 []
      │[ent-match] x->a and x->1
      │└── [ent-emp] x>0/\a=1 => T

      x->b |- x->a ==> a=b []
      │[ent-match] x->a and x->b
      │└── [ent-emp] x>0/\a=b => T

      y->c*x->b |- ex x. x->a ==> y=x/\a=c [x := y]
      │[ent-match] ex x. x->a
      │└── [ent-match-any] y->c and ex x. x->a
      │    └── [ent-emp] y>0/\y=x/\a=c => a=c

      y->3*x->2 |- ex x. x->1+1 ==> y=x/\1+1=3 [x := y]
      │[ent-match] ex x. x->1+1
      │└── [ent-match-any] y->3 and ex x. x->1+1
      │    └── [ent-emp] y>0/\y=x/\1+1=3 => 1+1=3 |}]
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

(* let debug = false *)
let ( let@ ) f x = f x

open Res.Backtrack

(** Given two heap formulae, matches points-to predicates
  may backtrack if the locations are quantified.
  returns (by invoking the continuation) when matching is complete (when right is empty).

  id: human-readable name
  vs: quantified variables
  k: continuation
*)
let rec check_qf2 :
    string -> string list -> state -> state -> (pi * pi -> pf) -> pf =
 fun id vs ante conseq k ->
  let a = Heap.normalize ante in
  let c = Heap.normalize conseq in
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
      | [] -> false
      | _ :: _ ->
        (* x is bound and could potentially be instantiated with anything on the right side, so try everything *)
        let r1 =
          any ~name:"ent-match-any"
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
        (* let  *)
        (* And (p1, Atomic (EQ, v, v1)) *)
        (* match *)
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
      | None -> false
      (* failwith
         (Format.asprintf "Heap.check: could not match %s->%s on RHS" x
            (string_of_term v)) *)
    end
    | None -> failwith (Format.asprintf "could not split LHS, bug?")
  end

let rec vars_in_term t =
  match t with
  | Num _ -> []
  | UNIT | TList _ | TTupple _ -> []
  | Plus (a, b) | Minus (a, b) -> vars_in_term a @ vars_in_term b
  | Var v -> [v]

let vars_in_pi pi =
  let rec aux pi =
    match pi with
    | Imply (a, b) | Or (a, b) | And (a, b) -> aux a @ aux b
    | Not a -> aux a
    | Atomic (_, a, b) -> vars_in_term a @ vars_in_term b
    | True | False | Predicate (_, _) -> []
  in
  aux pi

(** Recurses down a normalised staged spec, matching stages,
   translating away heap predicates to build a pure formula,
   and proving subsumption of each pair of stages.
   Residue from previous stages is assumed.

   Matching of quantified locations may cause backtracking.
   Other quantifiers are left to z3 to instantiate.
   
   i: index of stage
   all_vars: all quantified variables
*)
let rec check_staged_subsumption2 :
    int -> string list -> normalisedStagedSpec -> normalisedStagedSpec -> pf =
 fun i all_vars s1 s2 ->
  match (s1, s2) with
  | (es1 :: es1r, ns1), (es2 :: es2r, ns2) -> begin
    (* fail fast by doing easy checks first *)
    let c1, a1 = es1.e_constr in
    let c2, a2 = es2.e_constr in
    let* _ =
      let r = String.equal c1 c2 in
      if not r then Format.printf "FAIL, constr %s != %s@." c1 c2;
      r
    in
    let* _ =
      let l1 = List.length a1 in
      let l2 = List.length a2 in
      let r = l1 = l2 in
      if not r then Format.printf "FAIL, arg length %d != %d@." l1 l2;
      r
    in
    let* _ =
      let arg_eqs = conj (List.map2 (fun x y -> Atomic (EQ, x, y)) a1 a2) in
      let post2 =
        let p, h = es2.e_post in
        (conj [arg_eqs; p], h)
      in
      stage_subsumes
        (Format.asprintf "Eff %d" i)
        all_vars
        (es1.e_evars, (es1.e_pre, es1.e_post, es1.e_ret))
        (es2.e_evars, (es2.e_pre, post2, es2.e_ret))
    in
    check_staged_subsumption2 (i + 1) all_vars (es1r, ns1) (es2r, ns2)
  end
  | ([], ns1), ([], ns2) ->
    (* base case: check the normal stage at the end *)
    let (vs1, (p1, h1), (qp1, qh1), r1), (vs2, (p2, h2), (qp2, qh2), r2) =
      (ns1, ns2)
    in
    stage_subsumes "Norm" all_vars
      (vs1, ((p1, h1), (qp1, qh1), r1))
      (vs2, ((p2, h2), (qp2, qh2), r2))
  | _ ->
    Format.printf "FAIL, unequal length\n%s\n|=\n%s\n@."
      (string_of_normalisedStagedSpec s1)
      (string_of_normalisedStagedSpec s2);
    false

and stage_subsumes :
    string ->
    string list ->
    (state * state * term) quantified ->
    (state * state * term) quantified ->
    pf =
 fun what all_vars s1 s2 ->
  let vs1, (pre1, post1, ret1) = s1 in
  let vs2, (pre2, post2, ret2) = s2 in
  (* TODO replace uses of all_vars. this is for us to know if locations on the rhs are quantified. a smaller set of vars is possible *)
  (* contravariance *)
  let@ pre_l, pre_r = check_qf2 "pren" all_vars pre2 pre1 in
  let pre_res = Provers.entails_exists pre_l vs1 pre_r in
  Format.printf "(%s pre) %s => %s%s ==> %s@." what (string_of_pi pre_l)
    (string_of_existentials vs1)
    (string_of_pi pre_r) (string_of_res pre_res);
  let* _ = pre_res in
  (* cov *)
  let new_univ = vars_in_pi pre_l @ vars_in_pi pre_r in
  let vs22 = List.filter (fun v -> not (List.mem v new_univ)) vs2 in
  let res_v = verifier_getAfreeVar ~from:"res" () in
  let@ post_l, post_r = check_qf2 "postn" all_vars post1 post2 in
  (* TODO carry residue forward after this? *)
  let post_res =
    Provers.entails_exists
      (conj [pre_r; post_l; Atomic (EQ, Var res_v, ret1)])
      vs22
      (conj [post_r; Atomic (EQ, Var res_v, ret2)])
  in
  Format.printf "(%s post) %s => %s%s ==> %s@." what
    (string_of_pi (conj [pre_r; post_l]))
    (string_of_existentials vs22)
    (string_of_pi post_r) (string_of_res post_res);
  post_res

let extract_binders spec =
  let binders, rest =
    List.partition_map (function Exists vs -> Left vs | s -> Right s) spec
  in
  (List.concat binders, rest)

let rec unfold_predicate_aux pred prefix already s : disj_spec =
  match s with
  | [] -> List.map List.rev prefix
  | HigherOrder (_p, _h, (name, args), ret) :: s1
    when String.equal name pred.p_name && not (List.mem name already) ->
    (* unfold *)
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
  let init_prefix = [[]] in
  List.concat_map
    (fun s ->
      (* move all binders to the front, then unfold in the rest, so scope isn't changed. for example, if we have (ex a. b), and unfold (b = c \/ d), we don't want to get ((ex a. c) \/ (ex a.d)) *)
      (* unfortunately our representation does not allow this *)
      (* let binders, rest = extract_binders s in *)
      let rest = s in
      let res = unfold_predicate_aux pred init_prefix [] rest in
      res
      (* Exists binders :: res *))
    ds

let check_staged_subsumption : spec -> spec -> pf =
 fun n1 n2 ->
  (* proceed *)
  let es1, ns1 = normalise_spec n1 in
  let es2, ns2 = normalise_spec n2 in
  Format.printf "norm, subsumption\n%s\n|=\n%s\n@."
    (string_of_normalisedStagedSpec (es1, ns1))
    (string_of_normalisedStagedSpec (es2, ns2));
  (* check_staged_subsumption_ (es1, ns1) (es2, ns2) *)
  check_staged_subsumption2 0
    (Forward_rules.getExistientalVar (es1, ns1)
    @ Forward_rules.getExistientalVar (es2, ns2))
    (es1, ns1) (es2, ns2)

let apply_tactics ts lems preds (ds1 : disj_spec) (ds2 : disj_spec) =
  Format.printf "before tactics\n%s\n|=\n%s\n@." (string_of_disj_spec ds1)
    (string_of_disj_spec ds2);
  List.fold_left
    (fun t c ->
      let r =
        match c with
        | Unfold_right ->
          Format.printf "unfold right@.";
          let ds1, ds2 = t in
          let ds2 = List.fold_right unfold_predicate preds ds2 in
          (ds1, ds2)
        | Unfold_left ->
          Format.printf "unfold left@.";
          let ds1, ds2 = t in
          let ds1 = List.fold_right unfold_predicate preds ds1 in
          (ds1, ds2)
        | Apply l ->
          Format.printf "apply %s@." l;
          ( List.map
              (List.fold_right apply_lemma
                 (List.filter (fun le -> String.equal le.l_name l) lems))
              ds1,
            ds2 )
      in
      Format.printf "%s\n|=\n%s\n@."
        (string_of_disj_spec (fst r))
        (string_of_disj_spec (snd r));
      r)
    (ds1, ds2) ts

let before_solve : disj_spec -> disj_spec -> unit = fun _ _ -> ()

(**
  Subsumption between disjunctive specs.
  S1 \/ S2 |= S3 \/ S4
*)
let check_staged_subsumption_disj :
    tactic list -> lemma list -> pred_def list -> disj_spec -> disj_spec -> pf =
 fun ts lems preds ds1 ds2 ->
  let ds1, ds2 = apply_tactics ts lems preds ds1 ds2 in
  before_solve ds1 ds2;
  (* proceed *)
  all ds1 (fun s1 ->
      any ~name:"subsumes-disj-rhs-any" ds2 (fun s2 ->
          check_staged_subsumption s1 s2))

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
  Format.printf "%b@." (check_staged_subsumption_disj [] [] [] left right);
  Format.printf "%b@." (check_staged_subsumption_disj [] [] [] right left);
  [%expect {|
    before tactics
    ex q q1; req x->q; Norm(x->q1 /\ q1>q, 2)
    |=
    ex p; req x->p; Norm(x->p+1, 2)

    norm, subsumption
    ex q q1; req x->q; Norm(x->q1 /\ q1>q, 2)
    |=
    ex p; req x->p; Norm(x->p+1, 2)

    (Norm pre) T => ex q,q1. q=p ==> true
    (Norm post) q1>q/\q=p => q1>q/\p+1=q1 ==> false
    false
    before tactics
    ex p; req x->p; Norm(x->p+1, 2)
    |=
    ex q q1; req x->q; Norm(x->q1 /\ q1>q, 2)

    norm, subsumption
    ex p; req x->p; Norm(x->p+1, 2)
    |=
    ex q q1; req x->q; Norm(x->q1 /\ q1>q, 2)

    (Norm pre) T => ex p. p=q ==> true
    (Norm post) p=q => ex q1. q1=p+1/\q1>q ==> true
    true
          |}]
