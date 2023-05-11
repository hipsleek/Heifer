
let test1_true f
  (*@ ex r; f(1, r); Norm(emp, r) @*) =
  f 1

let test2_true f g
  (*@ ex r; ex s; f(1, r); g(2, s); Norm(emp, s) @*) =
  f 1;
  g 1

let test3_true f g
  (*@ ex r; ex s; f(1, r); g(r, s); Norm(emp, s) @*) =
  let x = f 1 in
  g x

let rec test4_true ()
  (*@ ex r; test4_true((), r); Norm(emp, r) @*) =
  test4_true ()

(*@ predicate test5_true(b, n, res) = Norm(res=0/\emp, res) \/ test5_true(b, n-1,res); Norm(emp, res) @*)

(*@ lemma ih = test5_true(b, n, r) => Norm(r=0/\emp, r) @*)

let[@proof unfold_right] rec test5_true b n
  (*@ ex r; test5_true(b, n, r); Norm(emp, r) @*) =
  if b then 0 else test5_true b (n - 1)
  (* explicit unfolding *)

let rec test6_true b n
  (*@ Norm(emp, 0) \/ ex r; test6_true(b, n-1, r); Norm(emp, r) @*) =
  if b then 0 else test6_true b (n - 1)
(* this is already unfolded *)

let rec test7_false b n
  (*@ ex r; test7_false(b, n, r); Norm(emp, r) @*) =
  if b then 0 else test7_false b (n - 1)
(* need explicit unfolding *)

let[@proof unfold_left; apply ih] rec test8_true b n
  (*@ Norm(emp, 0) @*) =
  test5_true b n
(* summarise *)

let[@proof unfold_left; apply ih] rec test9_false b n
  (*@ Norm(emp, 1) @*) =
  test5_true b n
(* summarise poorly *)

let[@proof unfold_left] rec test10_false b n
  (*@ Norm(emp, 0) @*) =
  test5_true b n
(* missing induction hypothesis *)
