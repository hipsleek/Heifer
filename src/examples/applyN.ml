
let rec applyN_unfolded f x n
(*@
  Norm(n=0/\emp, x) \/
  req n>0/\emp; ex r2; f(x, r2); ex r1; applyN(f, r2, n-1, r1); Norm(emp, r1)
@*)
=
if n = 0 then x
else let r = f x in applyN_unfolded f r (n-1)

(*@
  predicate applyN(f, x, n, res) =
    Norm(n=0/\x=res/\emp, res) \/
    req n>0/\emp; ex r; f(x, r); ex r1; applyN(f, r, n-1, r1); Norm(res=r1/\emp, r1)
@*)

let[@proof unfold_right] rec applyN f x n
(*@ ex r3; applyN(f, x, n, r3) @*)
=
if n = 0 then x
else let r = f x in applyN f r (n-1)

let incr x
(*@ Norm(emp, x+1) @*)
= x + 1

(*@
  predicate incr(x, res) =
    Norm(res=x+1/\emp, res)
@*)

(*@
  lemma ih = applyN(incr, x, n, res) => Norm(res=x+n/\emp, res)
@*)

let[@proof unfold_left; case 1 (apply ih)] sum ()
(*@ Norm(emp, 10) @*)
= applyN incr 0 10

let incr2 x
(*@ Norm(emp, x+2) @*)
= x + 2

(*@
  predicate incr2(x, res) =
    Norm(res=x+2/\emp, res)
@*)

(*@
  lemma ih2 = applyN(incr, x, n, res) => Norm(res=x+n+n/\emp, res)
@*)

let[@proof unfold_left; case 1 (apply ih2)] sum ()
(*@ Norm(emp, 20) @*)
= applyN incr2 0 10
