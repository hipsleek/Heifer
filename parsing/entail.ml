open Types
open Pretty

let string_of_option to_s o : string =
  match o with Some a -> "Some " ^ to_s a | None -> "None"

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
    let h, p1 = normaliseHeap h in
    (normalize_pure (And (p, p1)), h)

  (** given a nonempty heap formula, splits it into a points-to expression and another heap formula *)
  let rec split_one : kappa -> ((string * term) * kappa) option =
   fun h ->
    match h with
    | EmptyHeap -> None
    | PointsTo (x, v) -> Some ((x, v), EmptyHeap)
    | SepConj (a, b) -> begin
      match split_one a with None -> split_one b | Some r -> Some r
    end
    | MagicWand (_, _) -> failwith "cannot split magic wand"

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
    | MagicWand (_, _) -> failwith "cannot split_find magic wand"

  let rec xpure : kappa -> pi =
   fun h ->
    match h with
    | EmptyHeap -> True
    | PointsTo (x, _t) ->
      let v = verifier_getAfreeVar () in
      And (Atomic (EQ, Var v, Var x), Atomic (GT, Var v, Num 0))
    | SepConj (a, b) -> And (xpure a, xpure b)
    | MagicWand (_, _) -> failwith (Format.asprintf "xpure for magic wand")

  let rec check :
      kappa -> string list -> state -> state -> (proof * state, proof) result =
   fun k vs a c ->
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
        | Some (v1, h1') when v1 = v -> begin
          match check (SepConj (k, PointsTo (x, v))) vs (p1, h1') (p2, h2') with
          | Error s -> Error (rule ~children:[s] "[ent-match] %s" x)
          | Ok (pf, res) -> Ok (rule ~children:[pf] "[ent-match] %s" x, res)
        end
        | _ ->
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
    [%expect {|
      T /\ x->1 |- T /\ y->2 ==> FAIL
      │[ent-match] could not match y->2 on RHS

      T /\ x->1 |- T /\ x->1 ==> T /\ emp
      │[ent-match] x
      │└── [ent-emp]

      T /\ x->1*y->2 |- T /\ x->1 ==> T /\ emp
      │[ent-match] x
      │└── [ent-emp] |}]
end

let rec check_staged_entail : spec -> spec -> spec option =
 fun n1 n2 ->
  (* check_heap_entail (current_state n1) (current_state n2) *)
  Some (n1 @ n2)

and check_staged_subsumption : spec -> spec -> bool =
 fun n1 n2 ->
  match (n1, n2) with
  | [], [] -> true
  | d1 :: n3, d2 :: n4 ->
    (match (d1, d2) with
    | Require (p1, h1), Require (p2, h2) ->
      (* contravariance *)
      (match Heap.entails (p1, h1) (p2, h2) with
      | Ok _ -> true
      | Error _ -> false)
    | NormalReturn (p1, h1, _), NormalReturn (p2, h2, _) ->
      (* covariance *)
      (match Heap.entails (p1, h1) (p2, h2) with
      | Ok _ -> true
      | Error _ -> false)
    | _ -> failwith "unimplemented")
    && check_staged_subsumption n3 n4
  | _ -> false

(* let%expect_test "staged_entail" =
     let test l r = Format.printf "%s |= %s ==> %s@." (string_of_spec l) (string_of_spec r) (check_staged_entail l r |> string_of_option string_of_spec) in
     test [NormalReturn (PointsTo ("x", Num 1))] [NormalReturn (PointsTo ("x", Num 1))];
     [%expect {| x->1 |= x->1 ==> Some x->1; x->1 |}]

   let%expect_test "staged_subsumption" =
     let test l r = Format.printf "%s %s %s@." (string_of_spec l) (if check_staged_subsumption l r then "|--" else "|-/-") (string_of_spec r) in
     test [NormalReturn (PointsTo ("x", Num 1))] [NormalReturn (PointsTo ("x", Num 1))];
     [%expect {| x->1 |-- x->1 |}] *)

module Normalize = struct
  let rec sl_dom (h : kappa) =
    match h with
    | EmptyHeap -> []
    | PointsTo (s, _) -> [s]
    | SepConj (a, b) -> sl_dom a @ sl_dom b
    | MagicWand (a, b) -> sl_dom a @ sl_dom b

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

  (* let%expect_test "normalize" =
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
     test "rule 3 (TODO heap entailment)"
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

         --- rule 3 (TODO heap entailment)
         Norm(x->1 /\ T, ()); req T /\ x->2
         Norm(x->1 /\ T, ()); req T /\ x->2

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
         Norm(x->1*x->1 /\ T/\T, ()) |}] *)
end
