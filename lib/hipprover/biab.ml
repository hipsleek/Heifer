open Hipcore_typed
open Typedhip
open Syntax
open Utils
open Pretty
open Utils.Misc

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

(* precondition: all separation conjuctions are flatten into a list of conjucts *)
let rec match_points_to (ctx : biab_ctx) (ks1 : kappa list) (ks2 : kappa list) : kappa list * kappa list * kappa list * pi list =
  match ks1 with
  | [] -> [], ks2, [], []
  | PointsTo (x, t) as k :: ks1 ->
      (* we try to match on the location *)
      let match_loc = function
        | PointsTo (x', t') when x = x' -> Some t'
        | _ -> None
      in
      begin match Lists.find_delete_map match_loc ks2 with
      | None ->
          (* the location does not exists in the rhs *)
          (* therefore we add it into the rhs residue *)
          let common, anti_frame, frame, equalities = match_points_to ctx ks1 ks2 in
          common, anti_frame, k :: frame, equalities
      | Some (t', ks2) ->
          (* generate an equality here *)
          (* let ctx = if t = t' then ctx else {equalities = eq t t' :: ctx.equalities} in *)
          let common, anti_frame, frame, equalities = match_points_to ctx ks1 ks2 in
          let equalities = if t = t' then equalities else eq t t' :: equalities in
          k :: common, anti_frame, frame, equalities
      end
  | EmptyHeap :: _
  | SepConj _ :: _ -> failwith "match_points_to"

(* A * H1 |- H2 * D *)
(* the caller has h1 and h2 and therefore we don't need to return that *)
(* because we may have many solutions, that's why we need to use Iter.t.
   but I am not going to use it now *)
let solve (ctx : biab_ctx) (h1 : kappa) (h2 : kappa) : kappa list * kappa list * kappa list * pi list =
  let heap1 = conjuncts_of_kappa h1 in
  let heap2 = conjuncts_of_kappa h2 in
  (* now match h1 and h2 together. *)
  (* we need to match heap1 and heap2 together *)
  (* this is O(n^2) but do we do not care about efficiency atm *)
  (* if we can sort the conjucts and then do something like "merge"
     then the complexity of O(n log n) *)
  match_points_to ctx heap1 heap2

(* see Tests for more e2e tests, which would be nice to port here *)
let%expect_test _ =
  let test ctx h1 h2 =
    let common, anti_frame, frame, equalities = solve ctx h1 h2 in
    let common = sep_conj common in
    let anti_frame = sep_conj anti_frame in
    let frame = sep_conj frame in
    let equalities = conj equalities in
    Format.printf "%s * %s |- %s * %s\n%s@."
      (string_of_kappa anti_frame)
      (string_of_kappa common)
      (string_of_kappa common)
      (string_of_kappa frame)
      (string_of_pi equalities)
  in
  let _ =
    let h1 = points_to "x" (num 1) in
    let h2 = points_to "x" (num 1) in
    test emp_biab_ctx h1 h2;
    [%expect
      {|
      emp * x -> 1 |- x -> 1 * emp
      T
      |}]
  in
  let _ =
    let h1 = points_to "x" (num 1) in
    let h2 = points_to "y" (num 2) in
    test emp_biab_ctx h1 h2;
    [%expect
      {|
      y -> 2 * emp |- emp * x -> 1
      T
      |}]
  in
  let _ =
    let h1 = points_to "x" (var "a") in
    let h2 = points_to "x" (num 1) in
    test emp_biab_ctx h1 h2;
    [%expect
      {|
      emp * x -> a |- x -> a * emp
      a = 1
      |}]
  in
  let _ =
    let h1 = sep_conj [points_to "v14" (num 0); points_to "v15" (num 2)] in
    let h2 = sep_conj [points_to "v15" (plus (num 1) (num 1)); points_to "v14" (num 0)] in
    test emp_biab_ctx h1 h2;
    [%expect
      {|
      emp * v14 -> 0 * v15 -> 2 |- v14 -> 0 * v15 -> 2 * emp
      2 = 1 + 1
      |}]
  in
  ()
