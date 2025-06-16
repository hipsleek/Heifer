open Hipcore
open Hiptypes
open Syntax
open Utils
open Pretty

type biab_ctx = {
  equalities: pi list;
}

let emp_biab_ctx = {
  equalities = []
}

let string_of_biab_ctx ({equalities} : biab_ctx) : string =
  Format.sprintf
    "{equalities = %s}"
    (string_of_list string_of_pi equalities)

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
          k :: common, anti_frame, frame, ctx
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

(* see Tests for more e2e tests, which would be nice to port here *)
let%expect_test _ =
  let test ctx h1 h2 =
    let common, anti_frame, frame, ctx = solve ctx h1 h2 in
    let common = sep_conj common in
    let anti_frame = sep_conj anti_frame in
    let frame = sep_conj frame in
    Format.printf "%s * %s |- %s * %s\n%s@."
      (string_of_kappa anti_frame)
      (string_of_kappa common)
      (string_of_kappa common)
      (string_of_kappa frame)
      (string_of_biab_ctx ctx)
  in
  let _ =
    let h1 = points_to "x" (num 1) in
    let h2 = points_to "x" (num 1) in
    test emp_biab_ctx h1 h2;
    [%expect
      {|
      emp * x->1 |- x->1 * emp
      {equalities = []}
      |}]
  in
  let _ =
    let h1 = points_to "x" (num 1) in
    let h2 = points_to "y" (num 2) in
    test emp_biab_ctx h1 h2;
    [%expect
      {|
      y->2 * emp |- emp * x->1
      {equalities = []}
      |}]
  in
  ()
(*
  one (True, PointsTo ("x", Var "a")) (True, PointsTo ("x", Const (Num 1)));
  [%expect {| a=1 * x->a |- x->1 * 1=a |}];

  one (True, PointsTo ("x", Const (Num 1))) (True, PointsTo ("x", Const (Num 2)));
  [%expect {| failed |}]; *)
