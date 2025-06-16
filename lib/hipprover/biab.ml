open Hipcore
open Hiptypes
open Syntax
open Utils

type biab_ctx = {
  equalities: pi list;
}

let emp_biab_ctx = {
  equalities = []
}

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

let rec conjuncts_of_kappa (k : kappa) : kappa list =
  match k with
  | SepConj (k1, k2) -> conjuncts_of_kappa k1 @ conjuncts_of_kappa k2
  | _ -> [k]

(* precondition: all separation conjuctions are flatten into a list of conjucts *)
let rec match_points_to (ctx : biab_ctx) (ks1 : kappa list) (ks2 : kappa list) :
  kappa list * kappa list * kappa list * biab_ctx =
  match ks1 with
  | [] -> [], ks2, [], ctx
  | PointsTo (x, t) as k :: ks1 ->
      (* we try to match on the location *)
      let match_loc = function
        | PointsTo (x', _) -> x = x'
        | _ -> false
      in
      begin match Lists.find_delete_opt match_loc ks2 with
      | None ->
          (* the location does not exists in the rhs *)
          (* therefore we add it into the rhs residue *)
          let common, anti_frame, frame, ctx = match_points_to ctx ks1 ks2 in
          common, anti_frame, k :: frame, ctx
      | Some (PointsTo (_, t'), ks2) ->
          (* generate an equality here *)
          let ctx = if t = t' then ctx else {equalities = eq t t' :: ctx.equalities} in
          let common, anti_frame, frame, ctx = match_points_to ctx ks1 ks2 in
          common, anti_frame, frame, ctx
      | _ ->
          failwith "unreachable" (* TODO: rewrite this *)
      end
  | EmptyHeap :: _
  | SepConj _ :: _ -> failwith "match_points_to"

(* A * H1 |- H2 * D *)
(* the caller has h1 and h2 and therefore we don't need to return that *)
(* because we may have many solutions, that's why we need to use Iter.t.
   but I am not going to use it now *)
let solve (ctx : biab_ctx) (h1 : kappa) (h2 : kappa) : kappa list * kappa list * kappa list * biab_ctx =
  let heap1 = conjuncts_of_kappa h1 in
  let heap2 = conjuncts_of_kappa h2 in
  (* now match h1 and h2 together. *)
  (* we need to match heap1 and heap2 together *)
  (* this is O(n^2) but do we do not care about efficiency atm *)
  (* if we can sort the conjucts and then do something like "merge"
     then the complexity of O(n log n) *)
  match_points_to ctx heap1 heap2
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
