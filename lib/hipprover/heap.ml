
open Hipcore
open Hiptypes

(* let normalize : state -> state =
  fun (p, h) ->
  let h = simplify_heap h in
  (simplify_pure p, h) *)

(** given a nonempty heap formula, splits it into a points-to expression and another heap formula *)
let rec split_one (h : kappa) : ((string * term) * kappa) option =
  match h with
  | EmptyHeap -> None
  | PointsTo (x, t) -> Some ((x, t), EmptyHeap)
  | SepConj (a, b) ->
      match split_one a with
      | None -> split_one b
      | Some (c, r) -> Some (c, SepConj (r, b))

(** like split_one, but searches for a particular points-to *)
let rec split_find (n : string) (h : kappa) : (term * kappa) option =
  match h with
  | EmptyHeap -> None
  | PointsTo (x, t) ->
      if x = n then Some (t, EmptyHeap) else None
  | SepConj (a, b) ->
      match split_find n a with
      | Some (t, r) -> Some (t, SepConj (r, b))
      | None ->
          match split_find n b with
          | None -> None
          | Some (t, r) -> Some (t, SepConj (a, r))

let pairwise_var_inequality xs ys =
  let inequalities =
    List.concat_map
      (fun x ->
        List.filter_map
          (fun y ->
            if String.equal x y then None
            else Some (Not (Atomic (EQ, Var x, Var y))))
          ys)
      xs
  in
  Syntax.conj inequalities

let xpure (h : kappa) : pi =
  let rec run h =
    match h with
    | EmptyHeap -> (True, [])
    | PointsTo (x, _) -> (True, [x])
    | SepConj (a, b) ->
        let a, xs = run a in
        let b, ys = run b in
        (And (a, And (b, pairwise_var_inequality xs ys)), xs @ ys)
  in
  fst (run h)

let rec check :
  string ->
  string list ->
  state ->
  state ->
  (pi * pi * kappa -> 'a Search.t) ->
  'a Search.t =
fun id vs ante conseq k ->
let open Search in
(* TODO ptr equalities? *)
let a = (*normalize*) ante in
let c = (*normalize*) conseq in
(* debug ~at:1
  ~title:(Format.asprintf "SL entailment (%s)" id)
  "%s |- %s" (string_of_state ante) (string_of_state conseq); *)
(* TODO frame and spans *)
match (a, c) with
  | _ -> failwith "check"
(*
| (p1, h1), (p2, EmptyHeap) ->
  (* debug ~at:4 ~title:(Format.asprintf "right empty") ""; *)
  let left = And (xpure h1, p1) in
  (* TODO add more logging to surface what happens in these entailments *)
  k (left, p2, h1)
| (p1, h1), (p2, h2) -> begin
  (* we know h2 is non-empty *)
  match split_one h2 with
  | Some ((x, v), h2') when List.mem x vs ->
    (* debug ~at:4 ~title:(Format.asprintf "existential location %s" x) ""; *)
    let left_heap = list_of_heap h1 in
    (match left_heap with
    | [] -> fail
    | _ :: _ ->
      (* x is bound and could potentially be instantiated with anything on the right side, so try everything *)
      let r1 =
        any
          ~to_s:(fun (a, _) -> string_of_pair Fun.id string_of_term a)
          ~name:"ent-match-any"
          (left_heap |> List.map (fun a -> (a, (x, v))))
          (fun ((x1, v1), _) ->
            let _v2, h1' = split_find x1 h1 |> Option.get in
            (* ptr equality *)
            let _ptr_eq = Atomic (EQ, Var x1, Var x) in
            let triv = Atomic (EQ, v, v1) in
            (* matching ptr values are added as an eq to the right side, since we don't have a term := term substitution function *)
            check id vs (conj [p1], h1') (conj [p2; triv], h2') k)
      in
      r1)
  | Some ((x, v), h2') -> begin
    (* debug ~at:4 ~title:(Format.asprintf "free location %s" x) ""; *)
    (* x is free. match against h1 exactly *)
    match split_find x h1 with
    | Some (v1, h1') -> begin
      check id vs
        (conj [p1], h1')
        (conj [p2; And (p1, Atomic (EQ, v, v1))], h2')
        k
    end
    | None ->
      (* TODO *)
      (* debug ~at:4 ~title:(Format.asprintf "failed") ""; *)
      fail
  end
  | None -> failwith (Format.asprintf "could not split LHS, bug?")
end
*)

(* let%expect_test _ =
  let one ?ex h1 h2 =
    let on_ans (a, o, f) =
      Format.printf "%s |- %s * %s@.assumptions: %s@.obligations: %s@." (string_of_state h1) (string_of_state h2) (string_of_kappa f) (string_of_pi (Normalize.simplify_pure a)) (string_of_pi (Normalize.simplify_pure o))
    in
    (* TODO factor out this code which processes all answers *)
    let at_least_one = ref false in
    check "test" (Option.value ~default:[] ex) h1 h2 (fun (a, o, f) ->
      at_least_one := true;
      on_ans (a, o, f);
      (* continue to backtrack *)
      None) |> ignore;
    if not !at_least_one then
      Format.printf "%s |/- %s@." (string_of_state h1) (string_of_state h2)
  in
  one (True, PointsTo ("x", Num 1)) (True, PointsTo ("x", Num 1));
  [%expect {|
    x->1 |- x->1 * emp
    assumptions: T
    obligations: T
    |}];

  one (True, PointsTo ("x", Num 1)) (True, PointsTo ("x", Num 2));
  [%expect {|
    x->1 |- x->2 * emp
    assumptions: T
    obligations: 2=1
    |}];

  one (True, PointsTo ("x", Num 1)) (True, PointsTo ("y", Num 1));
  [%expect {| x->1 |/- y->1 |}];

  one (True, PointsTo ("x", Num 1)) (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2)));
  [%expect {| x->1 |/- x->1*y->2 |}];

  one (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2))) (True, PointsTo ("x", Num 1));
  [%expect {|
    x->1*y->2 |- x->1 * y->2
    assumptions: y>0
    obligations: T
    |}];

  (* Debug.init ~ctf:false ~org:false (Some "4"); *)
  one ~ex:["z"] (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 1))) (True, PointsTo ("z", Num 1));
  [%expect {|
    x->1*y->1 |- z->1 * y->1
    assumptions: y>0
    obligations: T
    x->1*y->1 |- z->1 * x->1
    assumptions: x>0
    obligations: T
    |}] *)
