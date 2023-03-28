
open Types
open Pretty

let rec effectStaged2Spec (effectStages:effectStage list ) : spec = 
  match effectStages with
  | [] -> []
  | (existiental, (p1, h1), (p2, h2), ins, ret) :: xs  -> 
    [Exists existiental; Require(p1, h1); RaisingEff(p2, h2, ins, ret)] @ effectStaged2Spec xs 

let normalStaged2Spec (normalStage:normalStage ) : spec = 
  match normalStage with
  | (existiental, (p1, h1), (p2, h2), ret)   -> 
    [Exists existiental; Require(p1, h1); NormalReturn(p2, h2, ret)] 


let normalisedStagedSpec2Spec (normalisedStagedSpec:normalisedStagedSpec) : spec  = 
  let (effS, normalS) = normalisedStagedSpec in 
  effectStaged2Spec effS @ normalStaged2Spec normalS

let string_of_option to_s o :string =
  match o with
  | Some a -> "Some " ^ to_s a
  | None -> "None"

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
    in loop EmptyHeap sp

let check_heap_entail : kappa -> kappa -> kappa option =
  fun n1 n2 ->
    match n1, n2 with
    | EmptyHeap, EmptyHeap -> Some EmptyHeap
    | PointsTo (s1, v1), PointsTo (s2, v2)
      when String.equal s1 s2 && v1 = v2 ->
        Some EmptyHeap
    | _, _ -> None

let rec check_staged_entail : spec -> spec -> spec option =
  fun n1 n2 ->
    (* check_heap_entail (current_state n1) (current_state n2) *)
    Some (n1 @ n2)

and check_staged_subsumption : spec -> spec -> bool =
  fun n1 n2 ->
    match n1, n2 with
    | [], [] -> true
    | d1 :: n3, d2 :: n4 ->
      begin match d1, d2 with
      | Require (_, h1), Require (_, h2) ->
        (* contravariance *)
        begin match check_heap_entail h2 h1 with
        | Some _ -> true
        | None -> false
        end
      | NormalReturn (_, h1, _), NormalReturn (_, h2, _) ->
        (* covariance *)
        begin match check_heap_entail h1 h2 with
        | Some _ -> true
        | None -> false
        end
      | _ -> failwith "unimplemented"
      end && check_staged_subsumption n3 n4
    | _ -> false

let%expect_test "heap_entail" =
  let test l r = Format.printf "%s |- %s ==> %s@." (string_of_kappa l) (string_of_kappa r) (check_heap_entail l r |> string_of_option string_of_kappa) in
  test (PointsTo ("x", Num 1)) (PointsTo ("x", Num 1));
  [%expect {| x->1 |- x->1 ==> Some emp |}]

(*

let%expect_test "staged_entail" =
  let test l r = Format.printf "%s |= %s ==> %s@." (string_of_spec l) (string_of_spec r) (check_staged_entail l r |> string_of_option string_of_spec) in
  test [Ensures (PointsTo ("x", Num 1))] [Ensures (PointsTo ("x", Num 1))];
  [%expect {| x->1 |= x->1 ==> Some x->1; x->1 |}]

let%expect_test "staged_subsumption" =
  let test l r = Format.printf "%s %s %s@." (string_of_spec l) (if check_staged_subsumption l r then "|--" else "|-/-") (string_of_spec r) in
  test [Ensures (PointsTo ("x", Num 1))] [Ensures (PointsTo ("x", Num 1))];
  [%expect {| x->1 |-- x->1 |}]

*)