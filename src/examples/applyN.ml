
let rec applyN_unfolded f x n
  (*@
    Norm(n=0/\emp, x) \/
    req n>0/\emp; ex r2; f(x, r2); ex r1; applyN(f, r2, n-1, r1); Norm(emp, r1)
  @*)
=
if n = 0 then x
else let r = f x in applyN_unfolded f r (n-1)

(*@ predicate applyN(f, x, n, res) =
  Norm(n=0/\emp, x) \/
  req n>0/\emp; ex r; f(x, r); ex r1; applyN(f, r, n-1, r1); Norm(emp, r1)
@*)

let[@proof unfold_right] rec applyN f x n
  (*@ ex r3; applyN(f, x, n, r3) @*)
=
if n = 0 then x
else let r = f x in applyN f r (n-1)

(* add ; Norm(emp, r3) *)
