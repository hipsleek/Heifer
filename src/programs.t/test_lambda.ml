

let f1 ()
(*@ ens res=(fun x r (*@ ens r=x @*) ) @*)
= let _ = () in
  fun x (*@ ens res=x @*) -> x

let f2 ()
(*@ ens res=2 @*)
=
  let f3 = f1 () in
  f3 2

let g f
(*@ req f <: (fun i r (*@ req i>9; ens r>=0/\r<=99 @*) );
    ens res>=0/\res<=99 @*)
= f 10

(*

How is this checked?

ex v1; f(10, v1); ens res=v1 <: req f=(fun i r -> req i>9; ens r=1); ens res=1

[expand left side]
req true; ens true; ex v1; f(10, v1); ens res=v1 <: req f=(fun i r -> req i>9; ens r=1); ens res=1

[contravariance of pre]
req f=... <: req true

[now we have the lambda in the ctx]
f=... |- ens true; ex v1; f(10, v1); ens res=v1 <: ens res=1

[unfold left]
f=... |- ens true; ex v1; req 10>9; ens v1=1; ens res=v1 <: ens res=1

[norm]
ens true; ex v1; req 10>9; ens v1=1/\res=v1 <: ens res=1

[simplify]
ens true; ex v1; req true; ens v1=1/\res=v1 <: ens res=1

ex v1; ens v1=1/\res=v1 <: ens res=1

*)

let main ()
(*@ ens res>=0/\res<=99 @*)
= g (fun x -> 1)


(*

Note: even though we know at the call site what f we're passing, we're limited by the post of g, which is in turn limited by the pre g imposes on f. Hence we can't give main the spec ens res=1.

How is this checked?

After applying the forward rules, we get this entailment because g is known:

ens f=(fun i r -> ens r=1);
req f <: (fun i r -> req i>9; ens r>=0/\r<=99);
ens res>=0/\res<=99
<:
ens res>=0/\res<=99

Focusing on the first two lines, pure abduction infers the entailment we're really interested in.

A /\ f=(fun i r -> ens r=1) |- f <: (fun i r -> req i>9; ens r>=0/\r<=99)

A = (fun i r -> ens r=1) <: (fun i r -> req i>9; ens r>=0/\r<=99)

The entailment is now:

req (fun i r -> ens r=1) <: (fun i r -> req i>9; ens r>=0/\r<=99);
ens res>=0/\res<=99
<:
ens res>=0/\res<=99

We extract subsumptions to check them separately, replacing them with true before sending pure formulae to the SMT solver.

*)