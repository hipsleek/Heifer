let rec applyN_unfolded f x n
(*@
  Norm(n=0/\emp, x) \/
  req n>0/\emp; ex r2; f(x, r2); ex r1; applyN_unfolded(f, r2, n-1, r1); Norm(emp, r1)
@*)
= if n = 0 then x
  else let r = f x in applyN_unfolded f r (n-1)

let rec applyN f x n =
  if n = 0 then x
  else let r = f x in applyN f r (n-1)

let incr x = x + 1

let sum ()
(*@ Norm(emp, 10) @*)
= applyN incr 0 10

let incr2 x = x + 2

let sum2 ()
(*@ Norm(emp, 20) @*)
= applyN incr2 0 10

let summary x n
(*@ ex r4; Norm(r4=x+n/\emp, r4) @*)
= applyN incr x n