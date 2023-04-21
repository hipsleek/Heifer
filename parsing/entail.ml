open Hiptypes
open Pretty

let string_of_pi p = string_of_pi (ProversEx.normalize_pure p)

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

module Res = struct
  let ( let* ) = Result.bind

  (* type 'a pf = proof * 'a option *)

  (** A proof tree or counterexample produced during search.
      Disjunction is not shown explicitly, so only successful disjuncts appear.
      If the proof fails, represents a counterexample, which shows one path to the failure. *)
  type 'a pf = (proof * 'a, proof) result

  let all :
      ?may_elide:bool ->
      name:string ->
      to_s:('a -> string) ->
      'a list ->
      ('a -> 'b pf) ->
      'b list pf =
   fun ?(may_elide = false) ~name ~to_s vs f ->
    let rec loop pfs rs vs =
      match vs with
      (* special case, just inline the rule *)
      | [] -> Ok (rule ~children:(List.rev pfs) ~name "", rs)
      | [x] when may_elide -> f x |> Result.map (fun (p, a) -> (p, [a]))
      | x :: xs ->
        let res = f x in
        (match res with
        | Error p ->
          Error (rule ~children:(List.rev (p :: pfs)) ~name "%s" (to_s x))
        | Ok (p, r) -> loop (p :: pfs) (r :: rs) xs)
    in
    loop [] [] vs

  let any :
      ?may_elide:bool ->
      name:string ->
      to_s:('a -> string) ->
      'a list ->
      ('a -> 'b pf) ->
      'b pf =
   fun ?(may_elide = false) ~name ~to_s vs f ->
    match vs with
    | [] ->
      (* Error (rule ~name "choice empty") *)
      failwith (Format.asprintf "choice empty: %s" name)
    | [x] when may_elide -> f x (* special case, just inline *)
    | v :: vs ->
      (* return the first non-failing result, or the last failure if all fail *)
      let rec loop v vs =
        let res = f v in
        match (res, vs) with
        | Ok (p, r), _ -> Ok (rule ~name ~children:[p] "%s" (to_s v), r)
        | Error p, [] -> Error (rule ~name ~children:[p] "%s" (to_s v))
        | Error _, v1 :: vs1 -> loop v1 vs1
      in
      loop v vs
end

open Res

let current_state : spec -> kappa =
 fun sp ->
  let rec loop current sp =
    match sp with
    | [] -> current
    | HigherOrder _ :: s -> loop EmptyHeap s
    | Exists _ :: s -> loop current s
    | Require _ :: s ->
      (* TODO look at this for pure constraints *)
      loop current s
    | NormalReturn (_, h, _) :: s -> loop (SepConj (current, h)) s
    | RaisingEff _ :: _ -> failwith "unimplemented"
  in
  loop EmptyHeap sp

type 'a quantified = string list * 'a

let string_of_quantified to_s (vs, e) =
  match vs with
  | [] -> to_s e
  | _ :: _ -> Format.asprintf "ex %s. %s" (String.concat " " vs) (to_s e)

type instantiations = (string * string) list

let string_of_instantiations kvs =
  List.map (fun (k, v) -> Format.asprintf "%s := %s" k v) kvs
  |> String.concat ", " |> Format.asprintf "[%s]"

module Heap = struct
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

  let conj xs =
    match xs with
    | [] -> True
    | x :: xs -> List.fold_right (fun c t -> And (c, t)) xs x

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

  (* let debug = false *)

  let rec check_qf2 :
      string -> pi -> string list -> state -> state -> (pi * pi) Res.pf =
   fun id eqs vs ante conseq ->
    let a = normalize ante in
    let c = normalize conseq in
    match (a, c) with
    | (p1, h1), (p2, EmptyHeap) ->
      let left = And (xpure h1, p1) in
      (* let valid = entails_exists ~debug:false left vs p2 in *)
      (* if valid then
         let pf =
           (* rule "xpure(%s * %s /\\ %s) => %s" (string_of_kappa h1)
              (string_of_kappa k) (string_of_pi p1) (string_of_pi p2) *)
           rule ~name:"ent-emp" "%s => ex %s. %s" (string_of_pi left)
             (String.concat " " vs) (string_of_pi p2)
         in *)
      (* Ok (pf, ((p1, h1), [])) *)
      Ok (rule ~name:"base" "base", (left, p2))
      (* else Error (rule ~name:"base" "base") *)
      (* rule ~name:"ent-emp" ~success:false "%s => ex %s. %s" *)
      (* (string_of_pi left) (String.concat " " vs) (string_of_pi p2) *)
    | (p1, h1), (p2, h2) -> begin
      (* we know h2 is non-empty *)
      match split_one h2 with
      | Some ((x, v), h2') when List.mem x vs ->
        let left_heap = list_of_heap h1 in
        (match left_heap with
        | [] ->
          Error
            (rule ~name:"ent-match-any" ~success:false
               "no more heap on the left to match %s->%s with" x
               (string_of_term v))
        | _ :: _ ->
          (* x is bound and could potentially be instantiated with anything on the right side, so try everything *)
          let r1 =
            Res.any ~name:"ent-match-any"
              ~to_s:(fun ((lx, lv), (rx, rv)) ->
                Format.asprintf "%s->%s and ex %s. %s->%s" lx
                  (string_of_term lv) rx rx (string_of_term rv))
              (left_heap |> List.map (fun a -> (a, (x, v))))
              (fun ((x1, v1), _) ->
                let _v2, h1' = split_find x1 h1 |> Option.get in
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
                let* pf, pi =
                  check_qf2 id (* (conj [eqs; ptr_eq]) *)
                    True vs
                    (* (conj [p1; fleq; unifier], h1') *)
                    (* (conj [p2; freq], h2') *)
                    (conj [p1], h1')
                    (conj [p2; triv], h2')
                in
                Ok (pf, pi))
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
          end)
      | Some ((x, v), h2') -> begin
        (* x is free. match against h1 exactly *)
        match split_find x h1 with
        | Some (v1, h1') -> begin
          (* let  *)
          (* And (p1, Atomic (EQ, v, v1)) *)
          match
            check_qf2 (* (SepConj (k, PointsTo (x, v))) *) id eqs vs
              (conj [p1], h1')
              (conj [p2], h2')
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

  let rec check_qf :
      kappa -> string list -> state -> state -> (state * instantiations) Res.pf
      =
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
          Res.any ~name:"ent-match-any"
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
      state quantified -> state quantified -> (state * instantiations) Res.pf =
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
      state quantified -> state quantified -> (state * instantiations) Res.pf =
   fun s1 s2 -> check_exists s1 s2

  let%expect_test "heap_entail" =
    verifier_counter_reset ();
    Pretty.colours := false;
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
  fun (vs, pre, post, (eff, t), ret) ->
    ( List.filter (fun v -> not (List.mem v names)) vs,
      instantiate_state bindings pre,
      instantiate_state bindings post,
      (eff, List.map (Forward_rules.instantiateTerms bindings) t),
      Forward_rules.instantiateTerms bindings ret )

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

let rec check_staged_subsumption_ :
    normalisedStagedSpec -> normalisedStagedSpec -> state pf =
 fun s1 s2 ->
  (* recurse down both lists in parallel *)
  match (s1, s2) with
  | (es1 :: es1r, ns1), (es2 :: es2r, ns2) -> begin
    let vs1, (p1, h1), (qp1, qh1), (nm1, _a1), r1 = es1 in
    let vs2, (p2, h2), (qp2, qh2), (nm2, _a2), r2 = es2 in
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

    (* covariance of postconditions *)
    let* pf2, ((_pr, _hr), inst2) =
      let qp1, qh1 = post in
      Heap.entails
        ( [],
          (And (qp1, And (pr, Atomic (EQ, r1, Var "res"))), SepConj (qh1, hr))
        )
        (vs2, (And (qp2, Atomic (EQ, r2, Var "res")), qh2))
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
    (* covariance *)
    let* pf2, ((pr, hr), _inst2) =
      Heap.entails
        ( vs1,
          (And (And (qp1, Atomic (EQ, Var "res", r1)), pr), SepConj (qh1, hr))
        )
        (vs2, (And (qp2, Atomic (EQ, Var "res", r2)), qh2))
    in
    (* unify return value *)
    let pure = Atomic (EQ, r1, r2) in
    Ok
      ( rule ~children:[pf1; pf2] ~name:"subsumption-base" "%s |= %s"
          (string_of_spec (normalStage2Spec ns1))
          (string_of_spec (normalStage2Spec ns2)),
        (And (pr, pure), hr) )
  | _ -> Error (rule ~name:"subsumption-stage" ~success:false "unequal length")

(* let show_fml (_ : pi list) = () *)

let rec check_staged_subsumption2 :
    int ->
    string list ->
    (string * pi) list ->
    normalisedStagedSpec ->
    normalisedStagedSpec ->
    state pf =
 fun i all_vars so_far s1 s2 ->
  match (s1, s2) with
  | (es1 :: es1r, ns1), (es2 :: es2r, ns2) -> begin
    let _vs1, (p1, h1), (qp1, qh1), (nm1, _a1), r1 = es1 in
    let _vs2, (p2, h2), (qp2, qh2), (nm2, _a2), r2 = es2 in

    let triv = Atomic (EQ, r1, r2) in

    (* contra *)
    let* _pf, (pre_l, pre_r) =
      Heap.check_qf2 (Format.asprintf "pre%d" i) True all_vars (p2, h2) (p1, h1)
    in
    (* cov *)
    let* _pf, (post_l, post_r) =
      Heap.check_qf2
        (Format.asprintf "post%d" i)
        True all_vars (qp1, qh1) (qp2, qh2)
    in
    (* TODO heap backtracking is not working because check_qf2 never fails, and the use of any is inside there *)
    let fml =
      [
        (Format.asprintf "pre stage %d" i, Imply (pre_l, pre_r));
        ( Format.asprintf "post stage %d" i,
          Imply (Heap.conj [post_l], Heap.conj [post_r; triv]) );
      ]
    in
    (* compare effect names *)
    let* _ =
      if String.equal nm1 nm2 then Ok ()
      else Error (rule ~name:"name-equal" "eff not equal")
    in
    let* _pf, res =
      check_staged_subsumption2 (i + 1) all_vars (fml @ so_far) (es1r, ns1)
        (es2r, ns2)
    in
    (* pf1; pf2; pf *)
    Ok
      ( rule ~children:[] ~name:"subsumption-stage" "%s |= %s"
          (string_of_spec (normalisedStagedSpec2Spec s1))
          (string_of_spec (normalisedStagedSpec2Spec s2)),
        res )
  end
  | ([], ns1), ([], ns2) ->
    (* base case: check the normal stage at the end *)
    let (_vs1, (p1, h1), (qp1, qh1), r1), (_vs2, (p2, h2), (qp2, qh2), r2) =
      (ns1, ns2)
    in

    (* contra *)
    let* _pf, (pre_l, pre_r) =
      Heap.check_qf2 "pren" True all_vars (p2, h2) (p1, h1)
    in
    (* cov *)
    let* _pf, (post_l, post_r) =
      Heap.check_qf2 "postn" True all_vars (qp1, qh1) (qp2, qh2)
    in
    let fml =
      [
        ("norm pre", Imply (pre_l, pre_r));
        ("norm post", Imply (post_l, post_r));
        ("norm res eq", Atomic (EQ, r1, r2));
      ]
    in

    let res =
      Provers.entails_exists True all_vars
        (Heap.conj (List.rev (List.map snd (fml @ so_far))))
    in
    let debug = true in
    if debug then begin
      Format.printf "%s\nz3: %s@."
        (string_of_quantified
           (fun a ->
             List.map
               (fun (c, f) -> Format.asprintf "%s // %s" (string_of_pi f) c)
               a
             |> String.concat "\n/\\ ")
           (all_vars, fml @ so_far))
        (if res then "valid" else "not valid")
    end;
    (* show_fml (fml @ so_far); *)
    if res then
      Ok
        ( rule ~children:[] ~name:"subsumption-base" "%s |= %s"
            (string_of_spec (normalStage2Spec ns1))
            (string_of_spec (normalStage2Spec ns2)),
          (True, EmptyHeap) )
    else Error (rule ~name:"subsumption-base" ~success:false "fail")
  | _ -> Error (rule ~name:"subsumption-stage" ~success:false "unequal length")

let check_staged_subsumption : spec -> spec -> state Res.pf =
 fun n1 n2 ->
  (* replace quantified variables on the left side with fresh variables *)
  let es1, ns1 =
    let norm = normalise_spec n1 in
    norm
    (* let vars = Forward_rules.getExistientalVar norm in
       let vars_fresh =
         List.map (fun v -> (v, Var (verifier_getAfreeVar ()))) vars
       in
       let es1, (_, pre, post, ret) = instantiate_existentials vars_fresh norm in
       ( List.map (fun (_, pre, post, eff, ret) -> ([], pre, post, eff, ret)) es1,
         ([], pre, post, ret) ) *)
  in
  let es2, ns2 = normalise_spec n2 in
  (* check_staged_subsumption_ (es1, ns1) (es2, ns2) *)
  check_staged_subsumption2 0
    (Forward_rules.getExistientalVar (es1, ns1)
    @ Forward_rules.getExistientalVar (es2, ns2))
    [] (es1, ns1) (es2, ns2)

let%expect_test "staged subsumption" =
  verifier_counter_reset ();
  let test name l r =
    let res = check_staged_subsumption l r in
    Format.printf "\n--- %s\n%s\n%s\n%s%s@." name (string_of_spec l)
      (match res with Ok _ -> "|--" | Error _ -> "|-/-")
      (string_of_spec r)
      (match res with
      | Ok (pf, residue) ->
        Format.asprintf "\n==> %s\n%s" (string_of_state residue)
          (string_of_proof pf)
      | Error pf -> Format.asprintf "\n%s" (string_of_proof pf))
  in
  test "identity"
    [
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 1), Var "r");
    ]
    [
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 1), Var "r");
    ];
  test "variables"
    [
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), Var "r");
    ]
    [
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 2), Var "r");
    ];
  test "contradiction?"
    [
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), Var "r");
    ]
    [
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 1), Var "r");
    ];
  test "eff stage"
    [
      RaisingEff
        (True, PointsTo ("x", Plus (Var "a", Num 1)), ("E", []), Var "r");
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), Var "r");
    ]
    [
      RaisingEff
        (True, PointsTo ("x", Plus (Var "a", Num 1)), ("E", []), Var "r");
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 1), Var "r");
    ];
  [%expect
    {|
    T=>T // norm pre
    /\ T=>T // norm post
    /\ r=r // norm res eq
    z3: valid

    --- identity
    req x->1; Norm(x->1, r)
    |--
    req x->1; Norm(x->1, r)
    ==> emp
    │[subsumption-base] req x->1; Norm(x->1, r) |= req x->1; Norm(x->1, r)

    T=>T // norm pre
    /\ T=>T // norm post
    /\ r=r // norm res eq
    z3: valid

    --- variables
    req x->a; Norm(x->a+1, r)
    |--
    req x->1; Norm(x->2, r)
    ==> emp
    │[subsumption-base] req x->a; Norm(x->a+1, r) |= req x->1; Norm(x->2, r)

    T=>T // norm pre
    /\ T=>T // norm post
    /\ r=r // norm res eq
    z3: valid

    --- contradiction?
    req x->a; Norm(x->a+1, r)
    |--
    req x->1; Norm(x->1, r)
    ==> emp
    │[subsumption-base] req x->a; Norm(x->a+1, r) |= req x->1; Norm(x->1, r)

    T=>T // norm pre
    /\ T=>T // norm post
    /\ r=r // norm res eq
    /\ T=>T // pre stage 0
    /\ T=>r=r // post stage 0
    z3: valid

    --- eff stage
    E(x->a+1, [], r); req x->a; Norm(x->a+1, r)
    |--
    E(x->a+1, [], r); req x->1; Norm(x->1, r)
    ==> emp
    │[subsumption-stage] E(x->a+1, [], r); req x->a; Norm(x->a+1, r) |= E(x->a+1, [], r); req x->1; Norm(x->1, r) |}]

(**
  Subsumption between disjunctive specs.
  S1 \/ S2 |= S3 \/ S4

  Currently just returns the residue for the RHS disjunct that succeeds and doesn't print anything.
*)
let subsumes_disj ds1 ds2 =
  Res.all ~may_elide:true ~name:"subsumes-disj-lhs-all" ~to_s:string_of_spec ds1
    (fun s1 ->
      Res.any ~may_elide:true ~name:"subsumes-disj-rhs-any" ~to_s:string_of_spec
        ds2 (fun s2 -> check_staged_subsumption s1 s2))

module Normalize = struct
  let rec sl_dom (h : kappa) =
    match h with
    | EmptyHeap -> []
    | PointsTo (s, _) -> [s]
    | SepConj (a, b) -> sl_dom a @ sl_dom b

  let intersect xs ys =
    List.fold_right (fun c t -> if List.mem c ys then c :: t else t) xs []

  let sl_disjoint h1 h2 =
    match intersect (sl_dom h1) (sl_dom h2) with [] -> true | _ -> false

  let normalize__ spec =
    let rec one_pass (s : spec) =
      match s with
      | [] | [_] -> (s, false)
      | s1 :: s2 :: ss ->
        let s3, c =
          match (s1, s2) with
          | Require (p1, h1), Require (p2, h2) ->
            (* rule 1 *)
            ([Require (And (p1, p2), SepConj (h1, h2))], true)
          | NormalReturn (p1, h1, r1), NormalReturn (p2, h2, r2) when r1 = r2 ->
            (* rule 2 *)
            (* the equality at the end is res=a /\ res=b *)
            ([NormalReturn (And (p1, p2), SepConj (h1, h2), r1)], true)
          | NormalReturn (p1, h1, r1), Require (p2, h2) ->
            (* rule 3 *)
            (* TODO vars *)
            let r = Heap.entails ([], (p1, h1)) ([], (p2, h2)) in
            begin
              match r with
              | Error _ when sl_disjoint h1 h2 ->
                (* rule 4 *)
                ([s2; s1], true)
              | Error _ -> ([s1; s2], false)
              | Ok (_pf, ((rp, rh), _inst)) ->
                ([NormalReturn (And (And (p1, p2), rp), rh, r1)], true)
            end
          | _, _ -> ([s1; s2], false)
        in
        let hd, tl = match s3 with [] -> ([], []) | h :: t -> ([h], t) in
        let s5, c1 = one_pass (tl @ ss) in
        (hd @ s5, c || c1)
    in
    if false then ProversEx.to_fixed_point one_pass spec
    else one_pass spec |> fst

  let%expect_test "normalize" =
    verifier_counter_reset ();
    let test name s =
      Format.printf "--- %s\n%s\n%s\n@." name (string_of_spec s)
        (normalize__ s |> string_of_spec)
    in
    test "inert"
      [
        Require (True, PointsTo ("x", Num 1));
        NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      ];
    test "rule 4"
      [
        NormalReturn (True, PointsTo ("x", Num 1), UNIT);
        Require (True, PointsTo ("y", Num 1));
      ];
    test "rule 3 (TODO prob wrong)"
      [
        NormalReturn (True, PointsTo ("x", Num 1), UNIT);
        Require (True, PointsTo ("x", Num 2));
      ];
    test "rule 1"
      [
        Require (True, PointsTo ("x", Num 2));
        Require (True, PointsTo ("y", Num 2));
      ];
    test "rule 1 weird"
      [
        Require (True, PointsTo ("x", Num 2));
        Require (True, PointsTo ("x", Num 2));
      ];
    test "rule 2"
      [
        NormalReturn (True, PointsTo ("x", Num 1), UNIT);
        NormalReturn (True, PointsTo ("y", Num 1), UNIT);
      ];
    test "rule 2 weird"
      [
        NormalReturn (True, PointsTo ("x", Num 1), UNIT);
        NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      ];
    [%expect
      {|
               --- inert
               req x->1; Norm(x->1, ())
               req x->1; Norm(x->1, ())

               --- rule 4
               Norm(x->1, ()); req y->1
               req y->1; Norm(x->1, ())

               --- rule 3 (TODO prob wrong)
               Norm(x->1, ()); req x->2
               Norm(T/\T/\2=1, ())

               --- rule 1
               req x->2; req y->2
               req x->2*y->2 /\ T/\T

               --- rule 1 weird
               req x->2; req x->2
               req x->2*x->2 /\ T/\T

               --- rule 2
               Norm(x->1, ()); Norm(y->1, ())
               Norm(x->1*y->1 /\ T/\T, ())

               --- rule 2 weird
               Norm(x->1, ()); Norm(x->1, ())
               Norm(x->1*x->1 /\ T/\T, ()) |}]
end
