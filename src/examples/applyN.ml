let rec applyN_unfolded f x n
(*@ Norm(n=0/\emp, x) \/
  req n>0/\emp; ex r2; f(x, r2); ex r1; applyN_unfolded(f, r2, n-1, r1); Norm(emp, r1) @*)
= if n = 0 then x
  else let r = f x in applyN_unfolded f r (n-1)

let rec applyN f x n =
  if n = 0 then x
  else let r = f x in applyN f r (n-1)

let incr x = x + 1

let unsound_false ()
(*@ Norm(emp, 9) @*)
= applyN incr 0 10

let summary x n
(*@ Norm(emp, x+n) @*)
= applyN incr x n

let summary1_false x n
(*@ ex r4; Norm(r4=x+n-1/\emp, r4) @*)
= applyN incr x n

let summary2_false x n
(*@ ex r4; Norm(r4=x+n+1/\emp, r4) @*)
= applyN incr x n