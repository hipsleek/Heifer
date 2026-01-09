open Core.Syntax
open Core.Pretty
open Constr

let rec find_delete_map (f : 'a -> 'b option) (xs : 'a list) :
    ('b * 'a list) option =
  match xs with
  | [] -> None
  | x :: xs ->
    (match f x with
    | Some y -> Some (y, xs)
    | None ->
      (match find_delete_map f xs with
      | None -> None
      | Some (y, xs') -> Some (y, x :: xs')))

(* precondition: all separation conjuctions are flatten into a list of conjucts *)
let rec match_points_to (ks1 : hprop list) (ks2 : hprop list) :
    hprop list * hprop list * hprop list * prop list =
  match ks1 with
  | [] -> ([], ks2, [], [])
  | (HPointsTo (x, t) as k) :: ks1 ->
    (* we try to match on the location *)
    let match_loc = function
      | HPointsTo (x', t') when equal_term x x' -> Some t'
      | _ -> None
    in
    begin match find_delete_map match_loc ks2 with
    | None ->
      (* the location does not exists in the rhs *)
      (* therefore we add it into the rhs residue *)
      let common, anti_frame, frame, equalities = match_points_to ks1 ks2 in
      (common, anti_frame, k :: frame, equalities)
    | Some (t', ks2) ->
      (* generate an equality here *)
      (* let ctx = if t = t' then ctx else {equalities = eq t t' :: ctx.equalities} in *)
      let common, anti_frame, frame, equalities = match_points_to ks1 ks2 in
      let equalities =
        if t = t' then equalities else PAtom (TBinop (Eq, t, t')) :: equalities
      in
      (k :: common, anti_frame, frame, equalities)
    end
  | HEmp :: _ | HSepConj _ :: _ -> failwith "match_points_to"
  | HPure _ :: _ -> failwith "hpure"

let rec split_sep_conj (k : hprop) : hprop list =
  match k with
  | HEmp -> []
  | HPointsTo _ -> [k]
  | HSepConj (k1, k2) -> split_sep_conj k1 @ split_sep_conj k2
  | HPure _ ->
    Format.printf "%a@." pp_hprop k;
    failwith "hpure"

(* A * H1 |- H2 * D *)
(* the caller has h1 and h2 and therefore we don't need to return that *)
(* because we may have many solutions, that's why we need to use Iter.t.
   but I am not going to use it now *)
let biab_aux (h1 : hprop) (h2 : hprop) =
  let heap1 = split_sep_conj h1 in
  let heap2 = split_sep_conj h2 in
  (* now match h1 and h2 together. *)
  (* we need to match heap1 and heap2 together *)
  (* this is O(n^2) but do we do not care about efficiency atm *)
  (* if we can sort the conjucts and then do something like "merge"
     then the complexity of O(n log n) *)
  match_points_to heap1 heap2

let biab h1 h2 =
  let _common, a, f, eqs = biab_aux h1 h2 in
  let f = sep_conj f in
  let a =
    match eqs with
    | [] -> sep_conj a
    | _ :: _ -> HSepConj (sep_conj a, HPure (conj eqs))
  in
  (f, a)

let fvar x = TSymbol { sym_name = x }
let points_to l v = HPointsTo (fvar l, v)
let num n = TInt n
let plus a b = TApp ("plus", [a; b])

(* see Tests for more e2e tests, which would be nice to port here *)
let%expect_test _ =
  let test h1 h2 =
    let common, anti_frame, frame, equalities = biab_aux h1 h2 in
    let common = sep_conj common in
    let anti_frame = sep_conj anti_frame in
    let frame = sep_conj frame in
    let equalities = conj equalities in
    Format.printf "%a * %a |- %a * %a\n%a@." pp_hprop anti_frame pp_hprop common
      pp_hprop common pp_hprop frame pp_prop equalities
  in
  let _ =
    let h1 = points_to "x" (num 1) in
    let h2 = points_to "x" (num 1) in
    test h1 h2;
    [%expect {|
      emp * x->1 |- x->1 * emp
      true
      |}]
  in
  let _ =
    let h1 = points_to "x" (num 1) in
    let h2 = points_to "y" (num 2) in
    test h1 h2;
    [%expect {|
      y->2 * emp |- emp * x->1
      true
      |}]
  in
  let _ =
    let h1 = points_to "x" (fvar "a") in
    let h2 = points_to "x" (num 1) in
    test h1 h2;
    [%expect {|
      emp * x->a |- x->a * emp
      a=1
      |}]
  in
  let _ =
    let h1 = sep_conj [points_to "v14" (num 0); points_to "v15" (num 2)] in
    let h2 =
      sep_conj [points_to "v15" (plus (num 1) (num 1)); points_to "v14" (num 0)]
    in
    test h1 h2;
    [%expect
      {|
      emp * v14->0 * v15->2 |- v14->0 * v15->2 * emp
      2=plus(1, 1)
      |}]
  in
  ()

let pairwise_var_inequality xs ys =
  let inequalities =
    List.concat_map
      (fun x ->
        List.filter_map
          (fun y -> if x = y then None else Some (PAtom (TBinop (Neq, x, y))))
          ys)
      xs
  in
  conj inequalities

let xpure (h : hprop) : prop =
  let rec run h =
    match h with
    | HEmp -> (PAtom TTrue, [])
    | HPointsTo (x, _) -> (PAtom (TBinop (Gt, x, TInt 0)), [x])
    | HSepConj (a, b) ->
      let a, xs = run a in
      let b, ys = run b in
      (PConj (a, PConj (b, pairwise_var_inequality xs ys)), xs @ ys)
    | HPure p -> (p, [])
  in
  fst (run h)
