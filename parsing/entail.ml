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
  let entails : kappa -> kappa -> kappa option =
   fun n1 n2 ->
    match (n1, n2) with
    | EmptyHeap, EmptyHeap -> Some EmptyHeap
    | PointsTo (s1, v1), PointsTo (s2, v2) when String.equal s1 s2 && v1 = v2 ->
      Some EmptyHeap
    | _, _ -> None

  let%expect_test "heap_entail" =
    let test l r =
      Format.printf "%s |- %s ==> %s@." (string_of_kappa l) (string_of_kappa r)
        (entails l r |> string_of_option string_of_kappa)
    in
    test (PointsTo ("x", Num 1)) (PointsTo ("x", Num 1));
    [%expect {| x->1 |- x->1 ==> Some emp |}]
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
    | Require (_, h1), Require (_, h2) ->
      (* contravariance *)
      (match Heap.entails h2 h1 with Some _ -> true | None -> false)
    | NormalReturn (_, h1, _), NormalReturn (_, h2, _) ->
      (* covariance *)
      (match Heap.entails h1 h2 with Some _ -> true | None -> false)
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
            let r = Heap.entails h1 h2 in
            begin
              match r with
              | None when sl_disjoint h1 h2 ->
                (* rule 4 *)
                ([s2; s1], true)
              | None -> ([s1; s2], false)
              | Some r -> ([NormalReturn (And (p1, p2), r, r1)], true)
            end
          | _, _ -> ([s1; s2], false)
        in
        let hd, tl = match s3 with [] -> ([], []) | h :: t -> ([h], t) in
        let s5, c1 = one_pass (tl @ ss) in
        (hd @ s5, c || c1)
    in
    let rec to_fixed_point spec =
      let spec, changed = one_pass spec in
      if not changed then spec else to_fixed_point spec
    in
    if false then to_fixed_point spec else one_pass spec |> fst

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
        Norm(x->1*x->1 /\ T/\T, ()) |}]
end
