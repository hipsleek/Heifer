(* let rec applyN f n x
(* applyN(f, n, x, r); Norm(emp, r) @*)
=
  if n = 0 then x
  else
    let r = f x in
    applyN f (n - 1) r *)

  (* Norm(emp, 0) \/ ex r; test5_true(b, n-1, r); Norm(emp, r) *)

(* [@proof unfold_right] *)

(*@ predicate test5_true(b, n, res) = Norm(res=0/\emp, res) \/ test5_true(b, n-1,res); Norm(emp, res) @*)

(*@ lemma ih = test5_true(b, n, r) => Norm(r=0/\emp, r) @*)

let[@proof unfold_right] rec test5_true b n
  (*@ ex r; test5_true(b, n, r); Norm(emp, r) @*) =
  if b then 0 else test5_true b (n - 1)
  (* explicit unfolding *)

let[@proof unfold_left; apply ih] rec test9_false b n
  (*@ Norm(emp, 1) @*) =
  test5_true b n
(* summarise poorly *)

   (*
let f () (*@ Norm(emp, 1) @*) = 1

let test6_true a  (*@ Norm(emp, 1) @*) =
  (* let j = 0 in *)
  (* j *)
  let j = f () in
  j
*)