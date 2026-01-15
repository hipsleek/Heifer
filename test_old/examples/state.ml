
(* https://ilyasergey.net/CS6217/_static/slides/04-FunLog.pdf *)
let min_max_plus x y min max
(*@ ex a b; req min->a*max->b; ex i j; ens min->i*max->j/\i<=j/\res=x+y @*)
= let min' = if x < y then x else y in
  let max' = if x < y then y else x in
  min := min';
  max := max';
  x + y