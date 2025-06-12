open Hipcore
open Hiptypes
open Pretty
open Subst
open Debug
open Syntax
open Utils
open Misc

type biab_ctx = {
  equivalance_class: unit list (* some kind of union-find structure *);
}

let emp_biab_ctx = {
  equivalance_class = []
}

(*
let pure_abduction left right =
  (* let@ _ =
    Debug.span (fun r ->
        debug ~at:5
          ~title:"pure_abduction"
          "%s /\\ ? |- %s\nabduced: %s\nnew left: %s\nnew right: %s" (string_of_pi left)
          (string_of_pi right)
          (string_of_result string_of_pi (map_presult (fun (a, _, _) -> a) r))
          (string_of_result string_of_pi (map_presult (fun (_, a, _) -> a) r))
          (string_of_result string_of_pi (map_presult (fun (_, _, a) -> a) r)))
  in *)
  (* woefully incomplete *)
  (* https://www.cs.utexas.edu/~isil/fmcad-tutorial.pdf *)
  (*
    A /\ a=b |- a <: c /\ F
    A: b <: c
    F: true
    ens a=b; req a<:c
    req b<:c; ens true
  *)
  let _eqs = find_equalities#visit_pi () left in
  (*
  let subs = find_subsumptions#visit_pi () right in
  let asmp =
    subs |> List.concat_map (fun (a, f) ->
      eqs |> List.concat_map (fun (b, c) ->
          (if b = a then [Subsumption (c, f), (b, c), (a, f)] else []) @
          (if c = a then [Subsumption (b, f), (b, c), (a, f)] else [])
        ))
  in
  let abduced = List.map (fun (a, _, _) -> a) asmp |> conj in
  let left1 =
    let used = List.map (fun (_, b, _) -> b) asmp in
    (remove_equalities used)#visit_pi () left
  in
  let right1 =
    let used = List.map (fun (_, _, c) -> c) asmp in
    (remove_subsumptions used)#visit_pi () right
  in
  (* more general case? *)
  (*
    A /\ a=1 |- a=2 /\ F
    A: 1=2
    F: true
    ens a=1; req a=2
    req 1=2; ens true
  *)
  abduced, left1, right1
  *)
  todo ()
*)

(** check if x=y is not invalid (i.e. sat) under the given assumptions *)
(*
let may_be_equal _assumptions _x _y =
  (* let@ _ =
       Debug.span (fun r ->
           debug ~at:4 ~title:"may be equal" "%s => %s = %s\n%s"
             (string_of_pi assumptions) (string_of_term x) (string_of_term y)
             (string_of_result string_of_bool r))
     in
     let tenv =
       Infer_types.infer_types_pi (create_abs_env ())
         (And (assumptions, Atomic (EQ, x, y)))
       |> Infer_types.concrete_type_env
     in
     let right = Atomic (EQ, x, y) in
     (* let eq = Provers.entails_exists tenv assumptions [] right in *)
     let eq = Provers.askZ3 tenv (Imply (assumptions, right)) in
     eq *)
  (* proving at this point is not effective as we may not be able to prove unsat, but later the constraints may be violated, resulting in false anyway. returning true here is just the worst case version of that *)
  true
*)

(* (x, t1) -* (y, t2), where li is a heap containing y *)
(* flag true => add to precondition *)
(* flag false => add to postcondition *)
(*
let rec deleteFromHeapListIfHas li (x, t1) existential flag assumptions :
    (string * term) list * pi =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:6
          ~title:"deleteFromHeapListIfHas"
          "(%s, %s) -* %s = %s\nex %s\nflag %b\nassumptions %s"
          x (string_of_term t1)
          (string_of_list (string_of_pair Fun.id string_of_term) li)
          (string_of_result (string_of_pair (string_of_list (string_of_pair Fun.id string_of_term)) string_of_pi) r)
          (string_of_list Fun.id existential)
          flag
          (string_of_pi assumptions))
  in
  let res =
    match li with
    | [] -> ([], True)
    | (y, t2) :: ys ->
      let same_loc =
        let exists_eq =
          List.mem x existential && List.mem y existential
          && may_be_equal True (Var x) (Var y)
        in
        String.equal x y || exists_eq
      in
      if same_loc then
        (* toggles whether or not z3 is used for equality checks. not using z3 is about 3x faster but causes unsoundness due to normalization not producing [req F]s if misses the fact that two values are not equal *)
        let fast_equality = false in
        begin
          match fast_equality with
          | true ->
            if stricTcompareTerm t2 (Var "_") then (ys, True)
            else (
              (* TODO these cases could be organised better... a few classes:
                 - one side is a variable
                 - both sides are variables
                 - both sides are obviously (un)equal
                 - both sides are not obviously equal (requiring z3 to check)
              *)
              match (t1, t2) with
              (* x-> z -* x-> 11   ~~~>  (emp, z=11) *)
              | Var t2Str, (Num _ | UNIT | TTrue | TFalse | Nil) ->
                if String.compare t2Str "_" == 0 then (ys, True)
                else (ys, Atomic (EQ, t1, t2))
              (* x->11 -* x-> z   ~~~>   (emp, true) *)
              | (Num _ | UNIT | TTrue | TFalse | Nil), Var t2Str ->
                if existStr t2Str existential then (ys, True)
                else (ys, Atomic (EQ, t1, t2))
              | Num a, Num b -> (ys, if a = b then True else raise Norm_failure)
              | UNIT, UNIT | TTrue, TTrue | TFalse, TFalse | Nil, Nil ->
                (ys, True)
              | _, _ ->
                if stricTcompareTerm t1 t2 || stricTcompareTerm t1 (Var "_")
                then (ys, True)
                else if flag then
                  (* ex a. x->a |- ex b. req x->b *)
                  (* a=b should be added in the result's postcondition.
                     this should be req (emp, true); ens emp, a=b *)
                  (ys, True)
                else (ys, Atomic (EQ, t1, t2))
                  (* | _, _ -> if flag then (ys, Atomic (EQ, t1, t2)) else (ys, True) *))
          | false ->
            (* handling the simple cases like this speeds things up by about 27% *)
            (match (t1, t2) with
            | Num a, Num b -> (ys, if a = b then True else raise Norm_failure)
            | Var a, Var b when a = b -> (ys, True)
            | UNIT, UNIT | TTrue, TTrue | TFalse, TFalse | Nil, Nil -> (ys, True)
            | _, _ ->
              ( ys,
                if may_be_equal assumptions t1 t2 then Atomic (EQ, t1, t2)
                else raise Norm_failure ))
        end
      else
        let res, uni =
          deleteFromHeapListIfHas ys (x, t1) existential flag assumptions
        in
        ((y, t2) :: res, uni)
  in
  let () =
    let sof = string_of_list (string_of_pair Fun.id string_of_term) in
    debug ~at:5 ~title:"delete from heap list" "%s -* %s = %s\nex %s"
      (string_of_pair Fun.id string_of_term (x, t1))
      (sof li)
      (string_of_pair sof string_of_pi res)
      (string_of_list Fun.id existential)
  in
  res
*)

(*
(* h1 * h |- h2, returns h and unificiation
   x -> 3 |- x -> z   -> (emp, true )
   x -> z |- x -> 3   -> (emp, z = 3)
*)
(* flag true => ens h1; req h2 *)
(* flag false => req h2; ens h1 *)
let normaliseMagicWand h1 h2 existential flag assumptions : kappa * pi =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:6
          ~title:"normaliseMagicWand"
          "%s * ?%s |- %s * ?%s\nex %s\nflag %b\nassumptions %s"
          (string_of_kappa h1)
          (string_of_result string_of_kappa (map_presult fst r))
          (string_of_kappa h2)
          (string_of_result string_of_pi (map_presult snd r))
          (string_of_list Fun.id existential)
          flag
          (string_of_pi assumptions))
  in
  let listOfHeap1 = list_of_heap h1 in
  let listOfHeap2 = list_of_heap h2 in
  let rec helper (acc : (string * term) list * pi) li =
    let heapLi, unification = acc in
    match li with
    | [] -> acc
    | (x, v) :: xs ->
      let heapLi', unification' =
        deleteFromHeapListIfHas heapLi (x, v) existential flag assumptions
      in
      helper (heapLi', And (unification, unification')) xs
  in
  let temp, unification = helper (listOfHeap2, True) listOfHeap1 in
  (simplify_heap (kappa_of_list temp), unification)
*)

let rec conjuncts_of_kappa (k : kappa) : kappa list =
  match k with
  | SepConj (k1, k2) -> conjuncts_of_kappa k1 @ conjuncts_of_kappa k2
  | _ -> [k]

(* precondition: all separation conjuctions are flatten into a list of conjucts *)
let rec match_points_to (ctx : biab_ctx) (ks1 : kappa list) (ks2 : kappa list) : kappa list * kappa list * biab_ctx =
  match ks1 with
  | [] -> ks2, [], ctx
  | (PointsTo (x, _t) as k) :: ks1 ->
      (* we try to match on the location *)
      let match_loc = function
        | PointsTo (x', _) -> x = x'
        | _ -> false
      in
      begin match Lists.find_delete_opt match_loc ks2 with
      | None ->
          (* the location does not exists in the rhs *)
          (* therefore we add it into the rhs residue *)
          let anti_frame, frame, ctx = match_points_to ctx ks1 ks2 in
          anti_frame, k :: frame, ctx
      | Some (_k', ks2) ->
        (* generate an equality here *)
          let ctx = ctx in
          let anti_frame, frame, ctx = match_points_to ctx ks1 ks2 in
          anti_frame, frame, ctx
      end
  | EmptyHeap :: _
  | SepConj _ :: _ -> failwith "match points to"

(* A * H1 |- H2 * D *)
(* the caller has h1 and h2 and therefore we don't need to return that *)
(* because we may have many solutions, that's why we need to use Iter.t.
   but I am not going to use it now *)
let solve (ctx : biab_ctx) (h1 : kappa) (h2 : kappa) : kappa list * kappa list * biab_ctx =
  ignore (ctx, h1, h2);
  let heap1 = conjuncts_of_kappa h1 in
  let heap2 = conjuncts_of_kappa h2 in
  (* now match h1 and h2 together. *)
  (* we need to match heap1 and heap2 together *)
  (* this is O(n^2) but do we do not care about efficiency atm *)
  (* if we can sort the conjucts and then do something like "merge"
     then the complexity of O(n log n) *)
  match_points_to ctx heap1 heap2
  (* if h1 = h2 then
    emp, emp, ctx
  else if h2 = emp then
    emp, h1, ctx
  else if (* b_ptr_match *) false then
    todo ()
  else
    match h1, h2 with
    | SepConj (h1_left, h1_right), SepConj (h2_left, h2_right) *)
(*
  let magicWandHeap, unification =
    normaliseMagicWand h2 h3 existential true (And (p2, p3))
  in
  (* not only need to get the magic wand, but also need to delete the common part from h2 *)
  let h2', unification1 =
    (* TODO equalities? *)
    normaliseMagicWand h3 h2 existential false (And (p2, p3))
    (* (pure_to_equalities p2) *)
  in
  let p4, p2, p3 = pure_abduction p2 p3 in
  debug ~at:5 ~title:"biabduction" "%s * %s |- %s * %s"
    (string_of_state (unification, magicWandHeap))
    (string_of_state (p2, h2))
    (string_of_state (p3, h3))
    (string_of_state (unification1, h2'));
  unification, magicWandHeap, unification1, h2', p4
*)

(*
(* see Tests for more e2e tests, which would be nice to port here *)
let%expect_test _ =
  let one ?uq h1 h2 =
    let unification, magicWandHeap, unification1, h2', p4 = solve (Option.value ~default:[] uq) h1 h2 in
    Format.printf "%s * %s |- %s * %s@."
      (string_of_state (Simpl.simplify_pure unification, magicWandHeap))
      (string_of_state h1)
      (string_of_state h2)
      (string_of_state (Simpl.simplify_pure (And (p4, unification1)), h2'));
  in
  one (True, PointsTo ("x", Const (Num 1))) (True, PointsTo ("x", Const (Num 1)));
  [%expect {| emp * x->1 |- x->1 * emp |}];

  one (True, PointsTo ("x", Const (Num 1))) (True, PointsTo ("y", Const (Num 2)));
  [%expect {| y->2 * x->1 |- y->2 * x->1 |}];

  one (True, PointsTo ("x", Var "a")) (True, PointsTo ("x", Const (Num 1)));
  [%expect {| a=1 * x->a |- x->1 * 1=a |}];

  one (True, PointsTo ("x", Const (Num 1))) (True, PointsTo ("x", Const (Num 2)));
  [%expect {| failed |}];
*)
