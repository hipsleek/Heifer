let rec applyN f x n  
=
if n == 0 then x 
else let r = f x in applyN f r (n-1)