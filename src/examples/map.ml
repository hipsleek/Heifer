
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let id y = y

let map_id ys (* FIXME *)
(*@ ens res=ys @*)
= map id ys

let succ x = x + 1

let map_not_id_false ys
(*@ ens res=ys @*)
= map succ ys

(* ghost function that specifies what mapping succ should return *)
let rec succ_list xs =
  match xs with
  | [] -> []
  | x :: xs1 -> succ x :: succ_list xs1

(* we use succ_list in the statement of this lemma *)
let map_succ ys (* FIXME *)
(*@ ex r; succ_list(ys, r); ens res=r @*)
= map succ ys

let rec length xs =
  match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let cl_map xs x
(*@ ex i; req x->i; ex r; length(xs, r); ex r1; ens x->i+r/\r1=xs/\res=r1 @*)
= let f a = x := !x + 1; a in
  map f xs

(*

Proof:

forall xs, x, res,
map(f, xs, res)
==>
ex i r; req x->i; length(xs, r); ens x->i+r /\ res=xs

[unfold map, then focus on base case, then recursive case]

----

Base case:

req emp; ens xs=[] /\ res=xs ==> ...

[unfold length on the right, pick the base case]

... ==> ex i; req x->i; ex r; ens x->i+r /\ xs=[] /\ r=0 /\ res=xs

[VCs]

x->i ==> emp * x->i

x->i * xs=[] /\ res=xs ==> ex r; ens x->i+r /\ xs=[] /\ r=0 /\ res=xs

----

Inductive case:

ex r hd tl; ens xs=hd::tl;
f(hd, r);
ex r1; map(f, tl, r1); ens res=r::r1
==>
ex i; req x->i; ex r; length(xs, r);
ens x->i+r /\ res=xs

[unfold f]

ex r hd tl; ens xs=hd::tl;
ex j; req x->j; ens x->j+1 /\ r=hd;
ex r1; map(f, tl, r1); ens res=hd::r1
==>
...

[unfold length on the right and choose the inductive case]

...
==>
ex i; req x->i; ex r;
ex lr xst; ens xs=_::xst; length(xst, lr); ens r=1+lr;
ens x->i+r /\ res=xs

[rewrite with IH]

ex r hd tl; ens xs=hd::tl;
ex j; req x->j; ens x->j+1 /\ r=hd;
ex r1;
ex i1 r2; req x->i1; length(tl, r2); ens x->i1+r2 /\ r1=tl;
ens res=hd::r1
==>
...

[norm using biabduction]

ex j; req x->j;
ex hd tl; ex r; ens xs=hd::tl /\ i1=j+1 /\ r=hd;
ex r1;
ex i1 r2; length(tl, r2); ens x->i1+r2 /\ r1=tl /\ res=hd::r1
==>
ex i; req x->i;
ex r; ex lr xst; ens xs=_::xst; length(xst, lr); ens r=1+lr /\ x->i+r /\ res=xs



*)

(* this cannot be proved because the final stage doesn't match after one unfolding *)
let cl_map_1_false ()
(*@ ens res=0 @*)=
  let y = ref 0 in
  cl_map [] y;
  !y

(* this cannot be proved because we bound the number of unfoldings.
   we could fully unfold if given finite constants perhaps *)
let cl_map_12_false ()
(*@ ens res=2 @*)=
  let y = ref 0 in
  cl_map [1;2] y;
  !y

let rec incr_list init li =
  match li with 
  | [] -> []
  | x :: xs -> 
    init :: incr_list (init + 1) xs

(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/map_vec.rs *)
let cl_map_incr_l xs x
(*@ ex i; req x->i; ex r; length(xs, r); ex r1; ens x->i+r/\res=r1 @*)
= let f a = x := !x + 1; !x in
  map f xs

let cl_map_incr_c xs x
(*@ ex i; req x->i; ex ys; ex j; ens j=i+1; incr_list(j, xs, ys); ens res=ys @*)
= let f a = x := !x + 1; !x in
  map f xs

(* Adapted from https://github.com/FabianWolff/closure-examples/blob/master/map_vec.rs *)
let rec thrice_list xs =
  match xs with
  | [] -> []
  | x :: xs' -> (x + x + x) :: thrice_list xs'

let map_thrice xs
(*@ ex ys; thrice_list(xs, ys); ens res=ys @*)
= let cl i = i + i + i in
  map cl xs
