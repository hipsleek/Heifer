open Types
open Pretty

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

module Res = struct
  let ( let* ) = Result.bind

  (* type 'a pf = proof * 'a option *)
  type 'a pf = (proof * 'a, proof) result
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

  let rec xpure : kappa -> pi =
   fun h ->
    match h with
    | EmptyHeap -> True
    | PointsTo (x, _t) ->
      let v = verifier_getAfreeVar () in
      And (Atomic (EQ, Var v, Var x), Atomic (GT, Var v, Num 0))
    | SepConj (a, b) -> And (xpure a, xpure b)

  let rec check : kappa -> string list -> state -> state -> state Res.pf =
   fun k vs a c ->
    (* TODO we are probably not normalizing in all the right places, and there is no preprocessing to uniquely name variables *)
    let a = normalize a in
    let c = normalize c in
    match (a, c) with
    | (p1, h1), (p2, EmptyHeap) ->
      let sat =
        askZ3_exists vs (Imply (And (xpure (SepConj (h1, k)), p1), p2))
      in
      if sat then
        let pf =
          (* rule "xpure(%s * %s /\\ %s) => %s" (string_of_kappa h1)
             (string_of_kappa k) (string_of_pi p1) (string_of_pi p2) *)
          rule "[ent-emp]"
        in
        Ok (pf, (p1, h1))
      else Error (rule "[ent-emp] FAIL")
    | (p1, h1), (p2, h2) -> begin
      (* we know h2 is non-empty *)
      match split_one h2 with
      | Some ((x, v), h2') -> begin
        (* match on h1 *)
        match split_find x h1 with
        | Some (v1, h1') -> begin
          match
            check
              (SepConj (k, PointsTo (x, v)))
              vs
              (And (p1, Atomic (EQ, v, v1)), h1')
              (p2, h2')
          with
          | Error s -> Error (rule ~children:[s] "[ent-match] %s" x)
          | Ok (pf, res) -> Ok (rule ~children:[pf] "[ent-match] %s" x, res)
        end
        | None ->
          Error
            (rule "[ent-match] could not match %s->%s on RHS" x
               (string_of_term v))
        (* failwith
           (Format.asprintf "Heap.check: could not match %s->%s on RHS" x
              (string_of_term v)) *)
      end
      | None -> failwith (Format.asprintf "could not split LHS, bug?")
    end

  let entails : state -> state -> (proof * state, proof) result =
   fun s1 s2 -> check EmptyHeap [] s1 s2

  let%expect_test "heap_entail" =
    let test l r =
      let res =
        match entails l r with
        | Error pf -> Format.asprintf "FAIL\n%s" (string_of_proof pf)
        | Ok (pf, residue) ->
          Format.asprintf "%s\n%s" (string_of_state residue)
            (string_of_proof pf)
      in
      Format.printf "%s |- %s ==> %s@." (string_of_state l) (string_of_state r)
        res
    in
    test (True, PointsTo ("x", Num 1)) (True, PointsTo ("y", Num 2));
    test (True, PointsTo ("x", Num 1)) (True, PointsTo ("x", Num 1));
    test
      (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2)))
      (True, PointsTo ("x", Num 1));
    test (True, PointsTo ("x", Num 1)) (True, PointsTo ("x", Var "a"));
    test (True, PointsTo ("x", Var "b")) (True, PointsTo ("x", Var "a"));
    [%expect
      {|
      x->1 |- y->2 ==> FAIL
      │[ent-match] could not match y->2 on RHS

      x->1 |- x->1 ==> 1=1
      │[ent-match] x
      │└── [ent-emp]

      x->1*y->2 |- x->1 ==> 1=1
      │[ent-match] x
      │└── [ent-emp]

      x->1 |- x->a ==> a=1
      │[ent-match] x
      │└── [ent-emp]

      x->b |- x->a ==> a=b
      │[ent-match] x
      │└── [ent-emp] |}]
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
    let rec loop : state -> effectStage list -> effectStage list -> state Res.pf
        =
     fun (pp1, ph1) es1 es2 ->
      (* recurse down both lists in parallel *)
      match (es1, es2) with
      | ( (_vs1, (p1, h1), (qp1, qh1), (n1, a1), r1) :: es1',
          (_vs2, (p2, h2), (qp2, qh2), (n2, a2), r2) :: es2' ) -> begin
        (* contravariance of preconditions *)
        let* _pf1, (pr, hr) =
          Heap.entails (And (pp1, p2), SepConj (ph1, h2)) (p1, h1)
        in
        (* covariance of postconditions *)
        let* _pf2, (pr, hr) =
          Heap.entails (And (qp1, pr), SepConj (qh1, hr)) (qp2, qh2)
        in
        (* compare effect names *)
        let* _ = if String.equal n1 n2 then Ok () else Error (rule "uh oh") in
        (* unify effect params and return value *)
        let unify =
          List.fold_right
            (fun (a, b) t -> And (t, Atomic (EQ, a, b)))
            (List.map2 (fun a b -> (a, b)) a1 a2)
            (Atomic (EQ, r1, r2))
        in
        let* pf, res = loop (And (unify, pr), hr) es1' es2' in
        Ok (rule ~children:[pf] "[subsumption-match]", res)
      end
      | [], [] ->
        (* base case: check the normal stage at the end *)
        let (_vs1, (p1, h1), (qp1, qh1), r1), (_vs2, (p2, h2), (qp2, qh2), r2) =
          (ns1, ns2)
        in
        (* contravariance *)
        let* _pf1, (pr, hr) =
          Heap.entails (And (pp1, p2), SepConj (ph1, h2)) (p1, h1)
        in
        (* covariance *)
        let* _pf2, (pr, hr) =
          Heap.entails (And (qp1, pr), SepConj (qh1, hr)) (qp2, qh2)
        in
        (* unify return value *)
        let pure = Atomic (EQ, r1, r2) in
        Ok (rule "[subsumption-base]", (And (pr, pure), hr))
      | _ -> Error (rule "FAIL unequal length")
    in
    loop (True, EmptyHeap) es1 es2

let%expect_test "staged subsumption" =
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
    │[subsumption-base]


    --- variables
    req x->a; Norm(x->a+1, r)
    |--
    req x->1; Norm(x->2, r)
    ==> 2=a+1/\a=1/\r=r
    │[subsumption-base]


    --- contradiction?
    req x->a; Norm(x->a+1, r)
    |--
    req x->1; Norm(x->1, r)
    ==> 1=a+1/\a=1/\r=r
    │[subsumption-base]


    --- eff stage
    E(x->a+1, [], r); req x->a; Norm(x->a+1, r)
    |--
    E(x->a+1, [], r); req x->1; Norm(x->1, r)
    ==> 1=a+1/\a=1/\r=r
    │[subsumption-match]
    │└── [subsumption-base] |}]

(**
  Subsumption between disjunctive specs.
  S1 \/ S2 |= S3 \/ S4

  Currently just returns the residue for the RHS disjunct that succeeds and doesn't print anything.
*)
let subsumes_disj ds1 ds2 =
  List.find_map
    (fun s2 ->
      let res = List.map (fun s1 -> check_staged_subsumption s1 s2) ds1 in
      let all_succeeded = List.for_all Result.is_ok res in
      if all_succeeded then
        Some (List.map2 (fun s1 r -> (s1, s2, Result.get_ok r)) ds1 res)
      else None)
    ds2

(* module Normalize = struct
     let rec sl_dom (h : kappa) =
       match h with
       | EmptyHeap -> []
       | PointsTo (s, _) -> [s]
       | SepConj (a, b) -> sl_dom a @ sl_dom b

     let intersect xs ys =
       List.fold_right (fun c t -> if List.mem c ys then c :: t else t) xs []

     let sl_disjoint h1 h2 =
       match intersect (sl_dom h1) (sl_dom h2) with [] -> true | _ -> false

     let normalize spec =
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
               let r = Heap.entails (p1, h1) (p2, h2) in
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
       let test name s =
         Format.printf "--- %s\n%s\n%s\n@." name (string_of_spec s)
           (normalize s |> string_of_spec)
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
            req T /\ x->1; Norm(x->1 /\ T, ())
            req T /\ x->1; Norm(x->1 /\ T, ())

            --- rule 4
            Norm(x->1 /\ T, ()); req T /\ y->1
            req T /\ y->1; Norm(x->1 /\ T, ())

            --- rule 3 (TODO prob wrong)
            Norm(x->1 /\ T, ()); req T /\ x->2
            Norm(emp /\ T/\T/\2=1, ())

            --- rule 1
            req T /\ x->2; req T /\ y->2
            req T/\T /\ x->2*y->2

            --- rule 1 weird
            req T /\ x->2; req T /\ x->2
            req T/\T /\ x->2*x->2

            --- rule 2
            Norm(x->1 /\ T, ()); Norm(y->1 /\ T, ())
            Norm(x->1*y->1 /\ T/\T, ())

            --- rule 2 weird
            Norm(x->1 /\ T, ()); Norm(x->1 /\ T, ())
            Norm(x->1*x->1 /\ T/\T, ()) |}]
   end *)

type star_entail = (stagedSpec list * state) * spec

let incremental_rules (pre : star_entail) (e : core_lang) =
  let _, _current = pre in
  match e with
  | CRead _v ->
    let _f = verifier_getAfreeVar () in
    (* Heap.entails current  *)
    failwith ""
  | CLet (_, _, _) -> failwith "not done"
  | CValue _ -> failwith "not done"
  | CIfELse (_, _, _) -> failwith "not done"
  | CFunCall (_, _) -> failwith "not done"
  | CWrite (_, _) -> failwith "not done"
  | CRef _ -> failwith "not done"
  | CAssert (_, _) -> failwith "not done"
  | CPerform (_, _) -> failwith "not done"
  | CMatch (_, _, _) -> failwith "not done"
  | CResume _ -> failwith "not done"
