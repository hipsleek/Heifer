
  $ ./landin.exe
  
  # declare
      {|
    landin_rec f =
      ex l knot.
        ens l->();
        ens knot=(fun n -> forall f1. req l->f1; ens l->f1; f f1 n);
        forall v0. req l->v0; ens l->knot;
        knot
  |}
  landin_rec declared
  
  # declare
      {|
    factf self n =
      ens n=0; 1
      \/ ens n>0; self (n-1); r1. n*.r1
  |}
  factf declared
  
  # start_proof
      {|
    forall n. is_int n =>
      landin_rec factf; f. f n <: ex l v. ens l->v; fact n
  |}
  
  ────────────────────────────────────────────────────────────
  forall n.
    is_int n =>
      landin_rec factf; f. f n <: (ex l v. ens l->v; fact n)
  
  
  # forall_intro ()
  
  n
  ────────────────────────────────────────────────────────────
  is_int n =>
    landin_rec factf; f. f n <: (ex l v. ens l->v; fact n)
  
  
  # intro_pure "Hty"
  
  n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     landin_rec factf; f. f n
  <: ex l v. ens l->v; fact n
  
  
  # unfold "landin_rec"
  
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
  
  
  # goal_is
      {|
       (ex l knot.
          ens l->();
          ens knot=(fun n1 ->
                     forall f1.
                       req l->f1; ens l->f1; factf f1 n1);
          (forall v0. req l->v0; ens l->knot; knot)); f.
         f n
    <: ex l v. ens l->v; fact n
          |}
  
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
  
  
  # exists_elim ()
  
  knot, l, n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     (ens l->();
      ens knot=(fun n1 ->
                 forall f1. req l->f1; ens l->f1; factf f1 n1);
      (forall v0. req l->v0; ens l->knot; knot)); f. 
       f n
  <: ex l v. ens l->v; fact n
  
  
  # simpl ()
  
  knot, l, n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     ens l->();
     ens knot=(fun n1 ->
                forall f1. req l->f1; ens l->f1; factf f1 n1);
     (forall v0. req l->v0; ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  # intro_heap ()
  
  knot, l, n
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     ens knot=(fun n1 ->
                forall f1. req l->f1; ens l->f1; factf f1 n1);
     (forall v0. req l->v0; ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  # intro_pure "Hknot"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     (forall v0. req l->v0; ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  # forall_elim ["()"]
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     (req l->(); ens l->knot; knot); f. f n
  <: ex l v. ens l->v; fact n
  
  
  # simpl ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     req l->(); ens l->knot; knot n
  <: ex l v. ens l->v; fact n
  
  
  # req_heap_elim ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     ens l->knot; knot n
  <: ex l v. ens l->v; fact n
  
  
  # simpl ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     ens l->knot; knot n
  <: ex l v. ens l->v; fact n
  
  
  # goal_is {|
       ens l->knot; knot n
    <: ex l v. ens l->v; fact n
  |}
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  ────────────────────────────────────────────────────────────
     ens l->knot; knot n
  <: ex l v. ens l->v; fact n
  
  
  # induction ~name:"IH" (`Int 0) "n"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l->knot; knot n
  <: ex l v. ens l->v; fact n
  
  
  # intro_heap ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     knot n
  <: ex l v. ens l->v; fact n
  
  
  # rewrite "Hknot"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     (fun n1 -> forall f1. req l->f1; ens l->f1; factf f1 n1)
       n
  <: ex l v. ens l->v; fact n
  
  
  # goal_is
      {|
       (fun n1 -> forall f1. req l->f1; ens l->f1; factf f1 n1)
         n
    <: ex l v. ens l->v; fact n
  |}
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     (fun n1 -> forall f1. req l->f1; ens l->f1; factf f1 n1)
       n
  <: ex l v. ens l->v; fact n
  
  
  # simpl ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     forall f1. req l->f1; ens l->f1; factf f1 n
  <: ex l v. ens l->v; fact n
  
  
  # forall_elim ["knot"]
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     req l->knot; ens l->knot; factf knot n
  <: ex l v. ens l->v; fact n
  
  
  # req_heap_elim ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l->knot; factf knot n
  <: ex l v. ens l->v; fact n
  
  
  # intro_heap ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     factf knot n
  <: ex l v. ens l->v; fact n
  
  
  # unfold "factf"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n=0; 1 \/ ens n>0; knot (n-1); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # disj_elim ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n=0; 1
  <: ex l v. ens l->v; fact n
  (1 more goals)
  
  
  # goal_is {|
    ens n=0; 1
    <: ex l v. ens l->v; fact n
  |}
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n=0; 1
  <: ex l v. ens l->v; fact n
  (1 more goals)
  
  
  # intro_pure "Hn"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n=0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     1
  <: ex l v. ens l->v; fact n
  (1 more goals)
  
  
  # exists_intro ["l"; "knot"]
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n=0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     1
  <: ens l->knot; fact n
  (1 more goals)
  
  
  # ens_heap_intro ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n=0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     1
  <: fact n
  (1 more goals)
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable knot
  Warning, file line 0, characters 0-0: unused variable l
  ==> Valid
  
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n>0; knot (n-1); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # goal_is
      {|
    ens n>0; knot (n-1); r1. n*.r1
    <: ex l v. ens l->v; fact n
  |}
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     ens n>0; knot (n-1); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # intro_pure "Hn"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l->knot
  ───────────────────────────────────────────────────────────*
     knot (n-1); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # revert_heap ()
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l->knot; knot (n-1); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # rewrite "IH"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  n-1>=0 /\ n-1<n
  (2 more goals)
  
  
  # prove ()
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
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  is_int (n-1)
  (1 more goals)
  
  
  # prove ()
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
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     (ex l v. ens l->v; fact (n-1)); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # goal_is
      "(ex l v. ens l->v; fact (n-1)); r1. n*.r1 <: ex l v. ens l->v; fact n"
  
  knot, l, n
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     (ex l v. ens l->v; fact (n-1)); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # exists_elim ()
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     (ens l1->v; fact (n-1)); r1. n*.r1
  <: ex l v. ens l->v; fact n
  
  
  # exists_intro ["l1"; "v"]
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     (ens l1->v; fact (n-1)); r1. n*.r1
  <: ens l1->v; fact n
  
  
  # simpl ()
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     ens l1->v; fact (n-1); r1. n*.r1
  <: ens l1->v; fact n
  
  
  # intro_heap ()
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
  l1->v
  ───────────────────────────────────────────────────────────*
     fact (n-1); r1. n*.r1
  <: ens l1->v; fact n
  
  
  # ens_heap_intro ()
  
  knot, l, l1, n, v
  Hknot: knot=(fun n ->
                forall f1. req l->f1; ens l->f1; factf f1 n)
  Hn: n>0
  Hty: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            ens l->knot; knot n1 <:
              (ex l1 v. ens l1->v; fact n1)
  ────────────────────────────────────────────────────────────
     fact (n-1); r1. n*.r1
  <: fact n
  
  
  # Options.show_why3_goal := true
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall knot : term, l : term, l1 : term, n : term, v : term.
        ((gt n (TInt 0)) = (TBool true))
          ->
          (n.is_int)
          ->
          ((times n ((minus n (TInt 1)).fact)) = (n.fact))
  end
  Warning, file line 0, characters 0-0: unused variable knot
  Warning, file line 0, characters 0-0: unused variable l
  Warning, file line 0, characters 0-0: unused variable l1
  Warning, file line 0, characters 0-0: unused variable v
  module M
    use Heifer
    constant n0 : int
    axiom H : 0 < n0
    goal goal1 :
      times (TInt n0) (fact1 (minus (TInt n0) (TInt 1))) = fact1 (TInt n0)
  end
  ==> Valid
  
  no more goals
  
  # qed ()
  no more goals
