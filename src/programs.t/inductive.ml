let rec applyN f n x
(*@ applyN(f, n, x, r); Norm(emp, r) @*)
=
  if n = 0 then x
  else
    let r = f x in
    applyN f (n - 1) r
