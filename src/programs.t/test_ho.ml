
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

let rec test5_true b n
  (*@ Norm(emp, 0) \/ ex r; test5_true(b, n-1, r); Norm(emp, r) @*) =
  if b then 0 else test5_true b (n - 1)
