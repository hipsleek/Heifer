open Types
open Pretty

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
    | [] -> failwith "choice must be nonempty"
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

(*
   Flatten Form
   ============
   S ::= req H | H & Norm | H & Eff | local v*
   N ::= \/ {S;..;S}
*)

let rec to_fixed_point f spec =
  let spec, changed = f spec in
  if not changed then spec else to_fixed_point f spec

let rec to_fixed_point_ptr_eq f spec =
  let spec1 = f spec in
  if spec == spec1 then spec else to_fixed_point_ptr_eq f spec

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

module Heap = struct
  (* let normalize_pure : pi -> pi =
     let rec once p =
       match p with
       | True | False | Atomic _ | Predicate _ -> (p, false)
       | And (a, b) ->
         let a1, c1 = once a in
         let b1, c2 = once b in
         if c1 || c2 then (And (a1, b1), true) else (p, false)
       | Or (a, b) ->
         let a1, c1 = once a in
         let b1, c2 = once b in
         if c1 || c2 then (Or (a1, b1), true) else (p, false)
       | Imply (a, b) ->
         let a1, c1 = once a in
         let b1, c2 = once b in
         if c1 || c2 then (Imply (a1, b1), true) else (p, false)
       | Not a ->
         let a1, c1 = once a in
         if c1 then (Not a1, true) else (p, false)
     in
     to_fixed_point once *)

  let normalize_pure : pi -> pi = normalPure

  (* let normalize_heap : kappa -> kappa * pi =
     fun h -> to_fixed_point_ptr_eq normaliseHeap h *)

  let normalize : state -> state =
   fun (p, h) ->
    let h = normaliseHeap h in
    (normalize_pure p, h)

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

  type 'a quantified = string list * 'a

  let string_of_quantified to_s (vs, e) =
    match vs with
    | [] -> to_s e
    | _ :: _ -> Format.asprintf "ex %s. %s" (String.concat " " vs) (to_s e)

  let rec check_qf : kappa -> string list -> state -> state -> state Res.pf =
   fun k vs ante conseq ->
    let a = normalize ante in
    let c = normalize conseq in
    match (a, c) with
    | (p1, h1), (p2, EmptyHeap) ->
      let fml = Imply (And (xpure (SepConj (h1, k)), p1), p2) in
      let sat = askZ3_exists_valid vs fml in
      if sat then
        let pf =
          (* rule "xpure(%s * %s /\\ %s) => %s" (string_of_kappa h1)
             (string_of_kappa k) (string_of_pi p1) (string_of_pi p2) *)
          rule ~name:"ent-emp" "%s" (string_of_pi fml)
        in
        Ok (pf, (p1, h1))
      else Error (rule ~name:"ent-emp" ~success:false "%s" (string_of_pi fml))
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
              check_qf
                (SepConj (k, PointsTo (x1, v1)))
                vs
                ( And
                    ( p1,
                      And
                        ( Atomic (EQ, Var x1, Var x),
                          And (Atomic (EQ, v, v2), Atomic (EQ, v, v1)) ) ),
                  h1' )
                (p2, h2'))
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

  let check_exists : state quantified -> state quantified -> state Res.pf =
   fun (avs, ante) (cvs, conseq) ->
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
      let p, h = conseq in
      let fresh_names =
        List.map (fun a -> (a, verifier_getAfreeVar ~from:a ())) cvs
      in
      let fresh_vars = List.map (fun (a, b) -> (a, Var b)) fresh_names in
      ( ( Forward_rules.instantiatePure fresh_vars p,
          Forward_rules.instantiateHeap fresh_vars h ),
        List.map snd fresh_names )
    in
    check_qf EmptyHeap vs left right

  let entails :
      state quantified -> state quantified -> (proof * state, proof) result =
   fun s1 s2 -> check_exists s1 s2

  let%expect_test "heap_entail" =
    verifier_counter_reset ();
    Pretty.colours := false;
    let test l r =
      let res =
        match entails l r with
        | Error pf -> Format.asprintf "FAIL\n%s" (string_of_proof pf)
        | Ok (pf, residue) ->
          Format.asprintf "%s\n%s" (string_of_state residue)
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

      x->1 |- x->1 ==> 1=1
      │[ent-match] x->1 and x->1
      │└── [ent-emp] T/\T/\f0=x/\f0>0/\1=1=>T

      x->1*y->2 |- x->1 ==> 1=1
      │[ent-match] x->1 and x->1
      │└── [ent-emp] T/\T/\f1=x/\f1>0/\1=1=>T

      x->1 |- x->a ==> a=1
      │[ent-match] x->a and x->1
      │└── [ent-emp] T/\T/\f2=x/\f2>0/\a=1=>T

      x->b |- x->a ==> a=b
      │[ent-match] x->a and x->b
      │└── [ent-emp] T/\T/\f3=x/\f3>0/\a=b=>T

      y->c*x->b |- ex x. x->a ==> a=c/\y=f4
      │[ent-match] ex f4. f4->a
      │└── [ent-match-any] y->c and ex f4. f4->a
      │    └── [ent-emp] T/\T/\f5=y/\f5>0/\a=c/\y=f4=>T

      y->3*x->2 |- ex x. x->1+1 ==> 1+1=3/\y=f6
      │[ent-match] ex f6. f6->1+1
      │└── [ent-match-any] y->3 and ex f6. f6->1+1
      │    └── [ent-emp] T/\T/\f7=y/\f7>0/\1+1=3/\y=f6=>T |}]
end

let check_staged_entail : spec -> spec -> spec option =
 fun n1 n2 ->
  let norm = normalise_spec (n1 @ n2) in
  Some (normalisedStagedSpec2Spec norm)

let check_staged_subsumption : spec -> spec -> state Res.pf =
  let open Res in
  fun n1 n2 ->
    let es1, ns1 = normalise_spec n1 in
    let es2, ns2 = normalise_spec n2 in
    let rec loop : state -> effectStage list -> effectStage list -> state pf =
     fun (acc_p1, acc_h1) es1 es2 ->
      (* recurse down both lists in parallel *)
      match (es1, es2) with
      | ( (vs1, (p1, h1), (qp1, qh1), (nm1, a1), r1) :: es1',
          (vs2, (p2, h2), (qp2, qh2), (nm2, a2), r2) :: es2' ) -> begin
        (* contravariance of preconditions *)
        let* pf1, (pr, hr) =
          Heap.entails
            ( vs2,
              ( And (acc_p1, And (p2, Atomic (EQ, r2, Var "res"))),
                SepConj (acc_h1, h2) ) )
            (vs1, (And (p1, Atomic (EQ, r1, Var "res")), h1))
        in
        (* covariance of postconditions *)
        let* pf2, (pr, hr) =
          Heap.entails
            ( vs1,
              ( And (qp1, And (pr, Atomic (EQ, r1, Var "res"))),
                SepConj (qh1, hr) ) )
            (vs2, (And (qp2, Atomic (EQ, r1, Var "res")), qh2))
        in
        (* compare effect names *)
        let* _ =
          if String.equal nm1 nm2 then Ok ()
          else Error (rule ~name:"name-equal" "uh oh")
        in
        (* unify effect params and return value *)
        let unify =
          List.fold_right
            (fun (a, b) t -> And (t, Atomic (EQ, a, b)))
            (List.map2 (fun a b -> (a, b)) a1 a2)
            True
        in
        let* pf, res = loop (And (unify, pr), hr) es1' es2' in
        Ok
          ( rule ~children:[pf1; pf2; pf] ~name:"subsumption-stage" "%s |= %s"
              (string_of_spec (effectStage2Spec es1))
              (string_of_spec (effectStage2Spec es2)),
            res )
      end
      | [], [] ->
        (* base case: check the normal stage at the end *)
        let (vs1, (p1, h1), (qp1, qh1), r1), (vs2, (p2, h2), (qp2, qh2), r2) =
          (ns1, ns2)
        in
        (* contravariance *)
        let* pf1, (pr, hr) =
          Heap.entails
            ( vs2,
              ( And (acc_p1, And (p2, Atomic (EQ, r1, Var "res"))),
                SepConj (acc_h1, h2) ) )
            (vs1, (And (p1, Atomic (EQ, r2, Var "res")), h1))
        in
        (* covariance *)
        let* pf2, (pr, hr) =
          Heap.entails
            ( vs1,
              ( And (qp1, And (pr, Atomic (EQ, r1, Var "res"))),
                SepConj (qh1, hr) ) )
            (vs2, (And (qp2, Atomic (EQ, r2, Var "res")), qh2))
        in
        (* unify return value *)
        let pure = Atomic (EQ, r1, r2) in
        Ok
          ( rule ~children:[pf1; pf2] ~name:"subsumption-base" "%s |= %s"
              (string_of_spec (normalStage2Spec ns1))
              (string_of_spec (normalStage2Spec ns2)),
            (And (pr, pure), hr) )
      | _ ->
        Error (rule ~name:"subsumption-stage" ~success:false "unequal length")
    in
    loop (True, EmptyHeap) es1 es2

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
    --- identity
    req x->1; Norm(x->1, r)
    |--
    req x->1; Norm(x->1, r)
    ==> 1=1/\r=r
    │[subsumption-base] req x->1; Norm(x->1, r) |= req x->1; Norm(x->1, r)
    │├── [ent-match] x->1 and x->1
    ││   └── [ent-emp] T/\T/\f0=x/\f0>0/\1=1=>T
    │└── [ent-match] x->1 and x->1
    │    └── [ent-emp] T/\T/\f1=x/\f1>0/\1=1=>T


    --- variables
    req x->a; Norm(x->a+1, r)
    |--
    req x->1; Norm(x->2, r)
    ==> 2=a+1/\a=1/\r=r
    │[subsumption-base] req x->a; Norm(x->a+1, r) |= req x->1; Norm(x->2, r)
    │├── [ent-match] x->a and x->1
    ││   └── [ent-emp] T/\T/\f2=x/\f2>0/\a=1=>T
    │└── [ent-match] x->2 and x->a+1
    │    └── [ent-emp] T/\T/\f3=x/\f3>0/\2=a+1/\a=1=>T


    --- contradiction?
    req x->a; Norm(x->a+1, r)
    |--
    req x->1; Norm(x->1, r)
    ==> 1=a+1/\a=1/\r=r
    │[subsumption-base] req x->a; Norm(x->a+1, r) |= req x->1; Norm(x->1, r)
    │├── [ent-match] x->a and x->1
    ││   └── [ent-emp] T/\T/\f4=x/\f4>0/\a=1=>T
    │└── [ent-match] x->1 and x->a+1
    │    └── [ent-emp] T/\T/\f5=x/\f5>0/\1=a+1/\a=1=>T


    --- eff stage
    E(x->a+1, [], r); req x->a; Norm(x->a+1, r)
    |--
    E(x->a+1, [], r); req x->1; Norm(x->1, r)
    ==> 1=a+1/\a=1/\r=r
    │[subsumption-stage] E(x->a+1, [], r) |= E(x->a+1, [], r)
    │├── [ent-emp] T/\T/\T=>T
    │├── [ent-match] x->a+1 and x->a+1
    ││   └── [ent-emp] T/\T/\f6=x/\f6>0/\a+1=a+1=>T
    │└── [subsumption-base] req x->a; Norm(x->a+1, r) |= req x->1; Norm(x->1, r)
    │    ├── [ent-match] x->a and x->1
    │    │   └── [ent-emp] T/\T/\f7=x/\f7>0/\a=1/\r=r=>T
    │    └── [ent-match] x->1 and x->a+1
    │        └── [ent-emp] T/\T/\f8=x/\f8>0/\1=a+1/\a=1=>T |}]

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
              | Ok (_pf, (rp, rh)) ->
                ([NormalReturn (And (And (p1, p2), rp), rh, r1)], true)
            end
          | _, _ -> ([s1; s2], false)
        in
        let hd, tl = match s3 with [] -> ([], []) | h :: t -> ([h], t) in
        let s5, c1 = one_pass (tl @ ss) in
        (hd @ s5, c || c1)
    in
    if false then to_fixed_point one_pass spec else one_pass spec |> fst

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
