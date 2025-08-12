
let test1_true f
  (*@ ex r. f(1, r); ens emp/\res=r @*) =
  f 1

(* disabled because this now raises an error due to g being undefined in the spec *)
(* let test1_false f *)
(*   (*@ ex r. g(1, r); ens emp/\res=r @*) = *)
(*   f 1 *)

let test2_true f g
  (*@ ex r s. f(1, r); g(1, s); ens emp/\res=s @*) =
  f 1;
  g 1

let test5_false f g
  (*@ ex r s. f(1, r); g(2, s); ens emp/\res=s @*) =
  f 1;
  g 1

let test3_true f g
  (*@ ex r s. f(1, r); g(r, s); ens emp/\res=s @*) =
  let x = f 1 in
  g x

let rec test4_true ()
  (*@ ex r. test4_true((), r); ens emp/\res=r @*) =
  test4_true ()

let rec test6_true b n
  (*@ ens emp/\res=0 \/ ex r. test6_true(b, n-1, r); ens emp/\res=r @*) =
  if b then 0 else test6_true b (n - 1)
(* this is already unfolded *)

let rec test7_false b n
  (*@ ex r. test7_false(b, n, r); ens emp/\res=r @*) =
  if b then 0 else test7_false b (n - 1)
(* need explicit unfolding *)

let compose_true f g x
(*@
  ex r_g. g(x, r_g);
  ex r_f. f(r_g, r_f);
  ens  emp/\res=r_f
@*)
= f (g x)

let compose_exists_true f g x
(*@
  ex r_g r_f.
  g(x, r_g);
  f(r_g, r_f);
  ens  emp/\res=r_f
@*)
= f (g x)
(* the positions of existentials matter and have to match the implementation, due to the way proving is done at each stage.
we optimize the positions of existentials automatically so this passes. *)
