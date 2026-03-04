(* open Heap
open Core.Pretty
open Core.Syntax
open Core.Syntax.Constr

let fvar x = Symbol { sym_name = x }
let points_to l v = PointsTo (fvar l, v)
let num n = Int n
let plus a b = Apply (Symbol { sym_name = "plus" }, [a; b])

(* see Tests for more e2e tests, which would be nice to port here *)
let%expect_test _ =
  let test h1 h2 =
    let common, anti_frame, frame, equalities = biab_aux h1 h2 in
    let common = sep_conj common in
    let anti_frame = sep_conj anti_frame in
    let frame = sep_conj frame in
    let equalities = conj equalities in
    Format.printf "%a * %a |- %a * %a\n%a@." pp_term anti_frame pp_term common
      pp_term common pp_term frame pp_term equalities
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
      2=plus 1 1
      |}]
  in
  () *)
