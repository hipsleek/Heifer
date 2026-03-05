open Core_lang

let dump_program ppf prog =
  let pp_list name ppf li =
    Format.fprintf ppf "%s: [@[" name;
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
      (fun ppf (name, body) -> Format.fprintf ppf "(%S, %a)" name Core_lang.dump_term body)
      ppf li;
    Format.fprintf ppf "]]@]"
  in
  Format.fprintf ppf "{ @[%a;@ %a @] }" (pp_list "pure_functions") prog.pure_functions
    (pp_list "program_functions") prog.program_functions

let test s =
  let prog = Frontend.parse_ocaml s in
  Format.printf "%a" dump_program prog

let%expect_test "basic let" =
  test "let f x y = x + y in f 1 2";
  [%expect
    {|
    { pure_functions: []];
      program_functions: [("()", Let ("f", Fun (["x"; "y"], Apply (Var "+", [Var "x"; Var "y"])), Apply (Var "f", [Int 1; Int 2])))]]  }
    |}]

let%expect_test "if and sequence" =
  test "let x = 1 in let f y = if y = 0 then x else x + y in f 2; f 0";
  [%expect
    {|
    { pure_functions: []];
      program_functions: [("()", Let ("x", Int 1, Let ("f", Fun (["y"], If (Apply (Var "=", [Var "y"; Int 0]), Var "x", Apply (Var "+", [Var "x"; Var "y"]))), Sequence (Apply (Var "f", [Int 2]), Apply (Var "f", [Int 0])))))]]  }
    |}]

let%expect_test "effects" =
  test "let f x = reset (shift k (f x); f 0) in perform (Eff x); continue k 1";
  [%expect
    {|
    { pure_functions: []];
      program_functions: [("()", Let ("f", Fun (["x"], Reset (Sequence (Shift ("k", Apply (Var "f", [Var "x"])), Apply (Var "f", [Int 0])))), Sequence (Perform ("Eff", Some (Var "x")), Resume ([Var "k"; Int 1]))))]]  }
    |}]

let%expect_test "pure functions and match" =
  let code =
    {|
let [@pure] rec length li =
  match li with
  | [] -> 0
  | x :: xs -> 1 + length xs

let rec foldr f li acc =
  match li with
  | [] -> acc
  | x :: xs -> f x (foldr f xs acc)
|}
  in
  test code;
  [%expect
    {|
    { pure_functions: [("length", Fun (["li"], Match (Var "li", [([](), Int 0); (::("x", "xs"), Apply (Var "+", [Int 1; Apply (Var "length", [Var "xs"])]))])))]];
      program_functions: [("foldr", Fun (["f"; "li"; "acc"], Match (Var "li", [([](), Var "acc"); (::("x", "xs"), Apply (Var "f", [Var "x"; Apply (Var "foldr", [Var "f"; Var "xs"; Var "acc"])]))])))]]  }
    |}]

let%expect_test "specifications in comments" =
  let code = {|
let foldr_sum xs k
(*@ sum(xs)+k @*)
= let g c t = c + t in
  foldr g xs k
|} in
  test code;
  [%expect
    {|
    { pure_functions: []];
      program_functions: [("foldr_sum", WithSpec (Fun (["xs"; "k"], Let ("g", Fun (["c"; "t"], Apply (Var "+", [Var "c"; Var "t"])), Apply (Var "foldr", [Var "g"; Var "xs"; Var "k"]))), " sum(xs)+k ", "foldr_sum"))]]  }
    |}]
