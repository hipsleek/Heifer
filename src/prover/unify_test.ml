open Unify
open Core.Syntax
open Core.Pretty
open Parsing.Parse
open Util.Strings

let pp_sigma ppf sigma =
  Fmt.pf ppf "@[<v>%a@]@,"
    (Fmt.list
       (Fmt.hovbox ~indent:2
          (Fmt.pair ~sep:(Fmt.any " := ") Fmt.string pp_term)))
    (List.map (fun (x, t) -> (Bindlib.name_of x, t)) (TVMap.bindings sigma))

let test_unify ?(ctx = SMap.empty) ?(uvars = TVSet.empty) input1 input2 =
  let t1 = parse_term ~ctx input1 in
  let t2 = parse_term ~ctx input2 in
  try
    let sigma = unify t1 t2 uvars in
    Format.printf "%a" pp_sigma sigma
  with
    Unification_failure msg -> Format.printf "Unification_failure: %s" msg

let%expect_test "unify" =
  let _ =
    test_unify "1" "1";
    [%expect {| |}]
  in
  let _ =
    test_unify "ens 1=1; ens 2=2" "ens 1=1; r. ens 2=2";
    [%expect {| Unification_failure: structure mismatch |}]
  in
  let _ =
    let t = new_tvar "t" in
    let ctx = SMap.of_list ["t", t] in
    let uvars = TVSet.of_list [t] in
    test_unify ~ctx ~uvars "forall x. t" "forall x. x=1";
    [%expect {| Unification_failure: escaped variable |}]
  in
  let _ =
    let f = new_tvar "f" in
    let ctx = SMap.of_list ["f", f] in
    let uvars = TVSet.of_list [f] in
    test_unify ~ctx ~uvars "forall x. f x" "forall x. x=1";
    [%expect {| f := (fun x -> x=1) |}]
  in
  let _ =
    let f = new_tvar "f" in
    let ctx = SMap.of_list ["f", f] in
    let uvars = TVSet.of_list [f] in
    test_unify ~ctx ~uvars "forall x y. f x" "forall x y. x+y=1";
    [%expect {| Unification_failure: escaped variable |}]
  in
  let _ =
    let f = new_tvar "f" in
    let ctx = SMap.of_list ["f", f] in
    let uvars = TVSet.of_list [f] in
    test_unify ~ctx ~uvars "forall x y. f x y" "forall x y. x=1";
    [%expect {| f := (fun x y -> x=1) |}]
  in
  ()

let%expect_test "unify_assoc" =
  ()
