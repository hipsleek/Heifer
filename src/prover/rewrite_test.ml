open Bindlib
open Rewrite
open Core.Syntax
open Core.Pretty
open Parsing.Parse

let%expect_test _ =
  let test rule term =
    let l = parse_term term in
    let r = rewrite rule l in
    Format.printf "%a ==> %a@." pp_term l pp_term r
  in

  let rule : rule = unbox (bind_mvar [||] (box_pair Mk.true_ Mk.false_)) in
  test rule "true";
  [%expect {| true ==> false |}];

  let id =
    let x = new_tvar "x" in
    Mk.fun_ (bind_mvar [| x |] (Mk.var x))
  in
  let rule : rule =
    unbox
      (bind_mvar [||]
         (box_pair
            (Mk.apply (Mk.symbol { sym_name = "f" }) (box_list [id]))
            (Mk.apply (Mk.symbol { sym_name = "g" }) (box_list [Mk.int 1]))))
  in
  test rule "f (fun x -> x)";
  [%expect {| f (fun x -> x) ==> g 1 |}];

  let const =
    let x = new_tvar "x" in
    let y = new_tvar "y" in
    Mk.fun_ (bind_mvar [| x; y |] (Mk.var x))
  in
  let rule : rule =
    unbox
      (bind_mvar [||]
         (box_pair
            (Mk.apply (Mk.symbol { sym_name = "f" }) (box_list [const]))
            (Mk.apply (Mk.symbol { sym_name = "g" }) (box_list [Mk.int 1]))))
  in
  test rule "f (fun x y -> x)";
  [%expect {| f (fun x y -> x) ==> g 1 |}];
