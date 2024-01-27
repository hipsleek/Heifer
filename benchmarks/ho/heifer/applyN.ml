let rec applyN f x n =
  if n = 0 then x
  else let r = f x in applyN f r (n-1)

let incr x = x + 1

let summary x n
(*@ ens res=x+n @*)
= applyN incr x n
