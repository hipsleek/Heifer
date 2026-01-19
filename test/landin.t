
  $ ./landin.exe
  landin_rec declared
  factf declared
  
  
  ────────────────────────────────────────────────────────────
  forall n.
    is_int n =>
      landin_rec factf; f. f n <: (ex l v. ens l->v; fact n)
  
  
  n
  ────────────────────────────────────────────────────────────
  is_int n =>
    landin_rec factf; f. f n <: (ex l v. ens l->v; fact n)
  
  
  n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     landin_rec factf; f. f n
  <: ex l v. ens l->v; fact n
  
  
  n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     (ex l knot.
        ens l->();
        ens knot=(fun n1 ->
                   forall f1.
                     req l->f1; ens l->f1; factf f1 n1);
        (forall v0. req l->v0; ens l->knot; knot)); f. 
       f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     (ens l->();
      ens knot=(fun n1 ->
                 forall f1. req l->f1; ens l->f1; factf f1 n1);
      (forall v0. req l->v0; ens l->knot; knot)); f. 
       f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     ens l->();
     ens knot=(fun n1 ->
                forall f1. req l->f1; ens l->f1; factf f1 n1);
     (forall v0. req l->v0; ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     ens knot=(fun n1 ->
                forall f1. req l->f1; ens l->f1; factf f1 n1);
     (forall v0. req l->v0; ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     (forall v0. req l->v0; ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     (req l->(); ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     req l->(); ens l->knot; knot; f. f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     ens l->knot; knot; f. f n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     ens l->knot; knot n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l->knot; knot n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     knot n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     (fun n1 -> forall f1. req l->f1; ens l->f1; factf f1 n1)
       n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     forall f1. req l->f1; ens l->f1; factf f1 n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     req l->knot; ens l->knot; factf knot n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l->knot; factf knot n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     factf knot n
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n=0; 1 \/ ens n>0; knot (n-1); r1. n*r1
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n=0; 1
  <: ex l v. ens l->v; fact n
  (1 more goals)
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n=0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     1
  <: ex l v. ens l->v; fact n
  (1 more goals)
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n=0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     1
  <: ens l->knot; fact n
  (1 more goals)
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n=0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     1
  <: fact n
  (1 more goals)
  
  Warning, file line 0, characters 0-0: unused variable knot
  Warning, file line 0, characters 0-0: unused variable l
  ==> Valid
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n>0; knot (n-1); r1. n*r1
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     knot (n-1); r1. n*r1
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l->knot; knot (n-1); r1. n*r1
  <: ex l v. ens l->v; fact n
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  n-1>=0 /\ n-1<n
  (1 more goals)
  
  Warning, file line 0, characters 0-0: unused variable knot
  Warning, file line 0, characters 0-0: unused variable l
  ==> Valid
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     (ex l v. ens l->v; fact (n-1)); r1. n*r1
  <: ex l v. ens l->v; fact n
  
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     (ens l1->v; fact (n-1)); r1. n*r1
  <: ex l v. ens l->v; fact n
  
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     (ens l1->v; fact (n-1)); r1. n*r1
  <: ens l1->v; fact n
  
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l1->v; fact (n-1); r1. n*r1
  <: ens l1->v; fact n
  
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l1->v
  ───────────────────────────────────────────────────────────*
     fact (n-1); r1. n*r1
  <: ens l1->v; fact n
  
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->knot; knot n1 <:
            (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     fact (n-1); r1. n*r1
  <: fact n
  
  Warning, file line 0, characters 0-0: unused variable knot
  Warning, file line 0, characters 0-0: unused variable l
  Warning, file line 0, characters 0-0: unused variable l1
  Warning, file line 0, characters 0-0: unused variable v
  ==> Valid
  
  no more goals
