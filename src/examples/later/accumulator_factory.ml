
(* https://rosettacode.org/wiki/Accumulator_factory *)

let accumulator init =
  let total = ref init in
  let acc x
  (*@ ex t; req total->t; ens total->t+x/\res=t+x @*)
  = total := !total + x; !total in
  acc

let test x n init (* FIXME *)
(*@ req n>=0; ens res=init+(n*.x) @*)
= assert (n >= 0);
  let acc = accumulator init in
  let rec repeat x k
  (*@
    req k=n; ex v; acc(0,v); req v=init+(n*.x); ens res=v
    \/ req 0<=k/\k<n;
       ex v; acc(x,v); req v=init+(k*.x+x);
       ex r; repeat(x,k+1,r); req r=init+(n*.x); ens res=r
  @*)
  = if k = n then acc 0
    else (acc x; repeat x (k + 1))
  in
  repeat x 0
