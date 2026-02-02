
  $ ./toss.exe
  
  # Options.fail_fast := true
  
  # axiom ~name:"eta_reduce" {| forall f. (fun x -> f x) <: f |}
  axiom eta_reduce declared
  
  # axiom ~name:"bind_id_r" {| forall t. t; x. x <: t |}
  axiom bind_id_r declared
  
  # axiom ~name:"conj_false_l" {| forall t. (false /\ t) = false |}
  axiom conj_false_l declared
  
  # axiom ~name:"conj_false_r" {| forall t. (t /\ false) = false |}
  axiom conj_false_r declared
  
  # axiom ~name:"conj_true_l" {| forall t. (true /\ t) = t |}
  axiom conj_true_l declared
  
  # axiom ~name:"conj_true_r" {| forall t. (t /\ true) = t |}
  axiom conj_true_r declared
  
  # axiom ~name:"conj_assoc"
      {| forall t1 t2 t3. ((t1 /\ t2) /\ t3) = (t1 /\ (t2 /\ t3)) |}
  axiom conj_assoc declared
  
  # declare {| incr x = forall v. req x->v; ens x->v+1 |}
  incr declared
  
  # declare
      {| do_toss x = shift k (incr x; k true; r1. incr x; k false; r2. r1 + r2) |}
  do_toss declared
  
  # declare
      {| toss x = reset (do_toss x; r. (ens r=true; 1 \/ ens r=false; 0)) |}
  toss declared
  
  # declare
      {|
      do_toss_n n x =
        ens n = 0; true \/
        ens n > 0; do_toss x; r1. do_toss_n (n-1) x; r2. r1 /\ r2
    |}
  do_toss_n declared
  
  # declare
      {| toss_n n x = reset (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0)) |}
  toss_n declared
  
  # lemma ~name:"do_toss_n_spec"
      {|
      forall n x a.
        reset (do_toss_n n x; r. (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
        forall v. req x->v; ens x->v+pow 2 (n+1)-2; (ens a=true; 1 \/ ens a=false; 0)
    |}
  
  ────────────────────────────────────────────────────────────
  forall n x a.
    reset
      (do_toss_n n x; r.
         (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      (forall v.
         req x->v;
         ens x->v+pow 2 (n+1)-2;
         (ens a=true; 1 \/ ens a=false; 0))
  
  
  # forall_intro ()
  
  a, n, x
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r.
          (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # revert "a"
  
  n, x
  ────────────────────────────────────────────────────────────
  forall a.
    reset
      (do_toss_n n x; r.
         (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      (forall v.
         req x->v;
         ens x->v+pow 2 (n+1)-2;
         (ens a=true; 1 \/ ens a=false; 0))
  
  
  # induction ~name:"IH" (`Int 0) "n"
  
  n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  forall a.
    reset
      (do_toss_n n x; r.
         (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      (forall v.
         req x->v;
         ens x->v+pow 2 (n+1)-2;
         (ens a=true; 1 \/ ens a=false; 0))
  
  
  # forall_intro ()
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r.
          (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # unfold "do_toss_n"
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     reset
       ((ens n=0; true
         \/ ens n>0;
            do_toss x; r1. do_toss_n (n-1) x; r2. r1 /\ r2);
          r. (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # unfold "do_toss"
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     reset
       ((ens n=0; true
         \/ ens n>0;
            shift k
              (incr x; k true; r2. incr x; k false; r3. r2+r3);
              r1. do_toss_n (n-1) x; r2. r1 /\ r2); r.
          (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # unfold "incr"
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     reset
       ((ens n=0; true
         \/ ens n>0;
            shift k
              ((forall v. req x->v; ens x->v+1);
               k true; r2.
                 (forall v. req x->v; ens x->v+1);
                 k false; r3. r2+r3); r1.
              do_toss_n (n-1) x; r2. r1 /\ r2); r.
          (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # shift_reset_reduce ()
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens n=0;
     (ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0)
     \/ ens n>0;
        (forall v.
           req x->v;
           ens x->v+1;
           reset
             ((fun r2 ->
                reset
                  ((do_toss_n (n-1) x; r4. r2 /\ r4); r3.
                     (ens (a /\ r3)=true; 1
                      \/ ens (a /\ r3)=false; 0))) true; r1.
                (forall v1. req x->v1; ens x->v1+1);
                (fun r3 ->
                  reset
                    ((do_toss_n (n-1) x; r5. r3 /\ r5); r4.
                       (ens (a /\ r4)=true; 1
                        \/ ens (a /\ r4)=false; 0))) false;
                  r2. r1+r2))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # simpl ()
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens n=0;
     (ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0)
     \/ ens n>0;
        (forall v.
           req x->v;
           ens x->v+1;
           reset
             (reset
                (do_toss_n (n-1) x; r2.
                   (ens (a /\ (true /\ r2))=true; 1
                    \/ ens (a /\ (true /\ r2))=false; 0));
                r1.
                (forall v1.
                   req x->v1;
                   ens x->v1+1;
                   reset
                     (do_toss_n (n-1) x; r3.
                        (ens (a /\ (false /\ r3))=true; 1
                         \/ ens (a /\ (false /\ r3))=false; 0));
                     r2. r1+r2)))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # shift_reset_reduce ()
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens n=0;
     (ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0)
     \/ ens n>0;
        (forall v.
           req x->v;
           ens x->v+1;
           reset
             (do_toss_n (n-1) x; r2.
                (ens (a /\ (true /\ r2))=true; 1
                 \/ ens (a /\ (true /\ r2))=false; 0)); r1.
             (forall v1.
                req x->v1;
                ens x->v1+1;
                reset
                  (do_toss_n (n-1) x; r3.
                     (ens (a /\ (false /\ r3))=true; 1
                      \/ ens (a /\ (false /\ r3))=false; 0));
                  r2. r1+r2))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # disj_elim ()
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens n=0;
     (ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0)
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # intro_pure "Hn"
  
  a, n, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # forall_intro ()
  
  a, n, v, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: req x->v;
     ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # intro_heap ()
  
  a, n, v, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # rewrite "Hn"
  
  a, n, v, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: ens x->v+pow 2 (0+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # have ~name:"H_eq" "v+pow 2 (0+1)-2 = v"
  
  a, n, v, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
  v+pow 2 (0+1)-2=v
  (2 more goals)
  
  
  # admit ()
  
  a, n, v, x
  H_eq: v+pow 2 (0+1)-2=v
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: ens x->v+pow 2 (0+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # rewrite "H_eq"
  
  a, n, v, x
  H_eq: v+pow 2 (0+1)-2=v
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: ens x->v; (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # clear_pure "H_eq"
  
  a, n, v, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: ens x->v; (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # elim_heap ()
  
  a, n, v, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens (a /\ true)=true; 1 \/ ens (a /\ true)=false; 0
  <: ens a=true; 1 \/ ens a=false; 0
  (1 more goals)
  
  
  # rewrite "conj_true_r"
  
  a, n, v, x
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens a=true; 1 \/ ens a=false; 0
  <: ens a=true; 1 \/ ens a=false; 0
  (1 more goals)
  
  
  # refl ()
  
  a, n, x
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens n>0;
     (forall v.
        req x->v;
        ens x->v+1;
        reset
          (do_toss_n (n-1) x; r2.
             (ens (a /\ (true /\ r2))=true; 1
              \/ ens (a /\ (true /\ r2))=false; 0)); r1.
          (forall v1.
             req x->v1;
             ens x->v1+1;
             reset
               (do_toss_n (n-1) x; r3.
                  (ens (a /\ (false /\ r3))=true; 1
                   \/ ens (a /\ (false /\ r3))=false; 0));
               r2. r1+r2))
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # intro_pure "Hn"
  
  a, n, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     forall v.
       req x->v;
       ens x->v+1;
       reset
         (do_toss_n (n-1) x; r2.
            (ens (a /\ (true /\ r2))=true; 1
             \/ ens (a /\ (true /\ r2))=false; 0)); r1.
         (forall v1.
            req x->v1;
            ens x->v1+1;
            reset
              (do_toss_n (n-1) x; r3.
                 (ens (a /\ (false /\ r3))=true; 1
                  \/ ens (a /\ (false /\ r3))=false; 0)); r2.
              r1+r2)
  <: forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  
  # forall_intro ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     forall v.
       req x->v;
       ens x->v+1;
       reset
         (do_toss_n (n-1) x; r2.
            (ens (a /\ (true /\ r2))=true; 1
             \/ ens (a /\ (true /\ r2))=false; 0)); r1.
         (forall v1.
            req x->v1;
            ens x->v1+1;
            reset
              (do_toss_n (n-1) x; r3.
                 (ens (a /\ (false /\ r3))=true; 1
                  \/ ens (a /\ (false /\ r3))=false; 0)); r2.
              r1+r2)
  <: req x->v;
     ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # intro_heap ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       reset
         (do_toss_n (n-1) x; r2.
            (ens (a /\ (true /\ r2))=true; 1
             \/ ens (a /\ (true /\ r2))=false; 0)); r1.
         (forall v1.
            req x->v1;
            ens x->v1+1;
            reset
              (do_toss_n (n-1) x; r3.
                 (ens (a /\ (false /\ r3))=true; 1
                  \/ ens (a /\ (false /\ r3))=false; 0)); r2.
              r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # forall_elim ["v"]
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     req x->v;
     ens x->v+1;
     reset
       (do_toss_n (n-1) x; r2.
          (ens (a /\ (true /\ r2))=true; 1
           \/ ens (a /\ (true /\ r2))=false; 0)); r1.
       (forall v1.
          req x->v1;
          ens x->v1+1;
          reset
            (do_toss_n (n-1) x; r3.
               (ens (a /\ (false /\ r3))=true; 1
                \/ ens (a /\ (false /\ r3))=false; 0)); r2.
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # elim_heap ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1;
     reset
       (do_toss_n (n-1) x; r2.
          (ens (a /\ (true /\ r2))=true; 1
           \/ ens (a /\ (true /\ r2))=false; 0)); r1.
       (forall v1.
          req x->v1;
          ens x->v1+1;
          reset
            (do_toss_n (n-1) x; r3.
               (ens (a /\ (false /\ r3))=true; 1
                \/ ens (a /\ (false /\ r3))=false; 0)); r2.
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # intro_heap ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n (n-1) x; r2.
          (ens (a /\ (true /\ r2))=true; 1
           \/ ens (a /\ (true /\ r2))=false; 0)); r1.
       (forall v.
          req x->v;
          ens x->v+1;
          reset
            (do_toss_n (n-1) x; r3.
               (ens (a /\ (false /\ r3))=true; 1
                \/ ens (a /\ (false /\ r3))=false; 0)); r2.
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # rewrite ~direction:Direction.rtl "conj_assoc"
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n (n-1) x; r2.
          (ens (a /\ true /\ r2)=true; 1
           \/ ens (a /\ true /\ r2)=false; 0)); r1.
       (forall v.
          req x->v;
          ens x->v+1;
          reset
            (do_toss_n (n-1) x; r3.
               (ens (a /\ false /\ r3)=true; 1
                \/ ens (a /\ false /\ r3)=false; 0)); r2.
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # rewrite "conj_true_r"
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n (n-1) x; r2.
          (ens (a /\ r2)=true; 1 \/ ens (a /\ r2)=false; 0));
       r1.
       (forall v.
          req x->v;
          ens x->v+1;
          reset
            (do_toss_n (n-1) x; r3.
               (ens (a /\ false /\ r3)=true; 1
                \/ ens (a /\ false /\ r3)=false; 0)); r2.
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # rewrite "conj_false_r"
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n (n-1) x; r2.
          (ens (a /\ r2)=true; 1 \/ ens (a /\ r2)=false; 0));
       r1.
       (forall v.
          req x->v;
          ens x->v+1;
          reset
            (do_toss_n (n-1) x; r3.
               (ens (false /\ r3)=true; 1
                \/ ens (false /\ r3)=false; 0)); r2. 
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # rewrite "IH"
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
  n-1>=0 /\ n-1<n
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  Warning, file line 0, characters 0-0: unused variable a
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     (forall v.
        req x->v;
        ens x->v+pow 2 (n-1+1)-2;
        (ens a=true; 1 \/ ens a=false; 0)); r1.
       (forall v.
          req x->v;
          ens x->v+1;
          reset
            (do_toss_n (n-1) x; r3.
               (ens (false /\ r3)=true; 1
                \/ ens (false /\ r3)=false; 0)); r2. 
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # rewrite "IH"
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
  n-1>=0 /\ n-1<n
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  Warning, file line 0, characters 0-0: unused variable a
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     (forall v.
        req x->v;
        ens x->v+pow 2 (n-1+1)-2;
        (ens a=true; 1 \/ ens a=false; 0)); r1.
       (forall v.
          req x->v;
          ens x->v+1;
          (forall v1.
             req x->v1;
             ens x->v1+pow 2 (n-1+1)-2;
             (ens false=true; 1 \/ ens false=false; 0)); r2.
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # forall_elim ["v+1"]
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     (req x->v+1;
      ens x->v+1+pow 2 (n-1+1)-2;
      (ens a=true; 1 \/ ens a=false; 0)); r1.
       (forall v1.
          req x->v1;
          ens x->v1+1;
          (forall v2.
             req x->v2;
             ens x->v2+pow 2 (n-1+1)-2;
             (ens false=true; 1 \/ ens false=false; 0)); r2.
            r1+r2)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # simpl ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     req x->v+1;
     ens x->v+1+pow 2 (n-1+1)-2;
     (ens a=true;
      (forall v1.
         req x->v1;
         ens x->v1+1;
         (forall v2.
            req x->v2;
            ens x->v2+pow 2 (n-1+1)-2;
            (ens false=true; 1+1 \/ ens false=false; 1+0)))
      \/ ens a=false;
         (forall v1.
            req x->v1;
            ens x->v1+1;
            (forall v2.
               req x->v2;
               ens x->v2+pow 2 (n-1+1)-2;
               (ens false=true; 0+1 \/ ens false=false; 0+0))))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # elim_heap ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1+pow 2 (n-1+1)-2;
     (ens a=true;
      (forall v1.
         req x->v1;
         ens x->v1+1;
         (forall v2.
            req x->v2;
            ens x->v2+pow 2 (n-1+1)-2;
            (ens false=true; 1+1 \/ ens false=false; 1+0)))
      \/ ens a=false;
         (forall v1.
            req x->v1;
            ens x->v1+1;
            (forall v2.
               req x->v2;
               ens x->v2+pow 2 (n-1+1)-2;
               (ens false=true; 0+1 \/ ens false=false; 0+0))))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # intro_heap ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2
  ───────────────────────────────────────────────────────────*
     ens a=true;
     (forall v.
        req x->v;
        ens x->v+1;
        (forall v1.
           req x->v1;
           ens x->v1+pow 2 (n-1+1)-2;
           (ens false=true; 1+1 \/ ens false=false; 1+0)))
     \/ ens a=false;
        (forall v.
           req x->v;
           ens x->v+1;
           (forall v1.
              req x->v1;
              ens x->v1+pow 2 (n-1+1)-2;
              (ens false=true; 0+1 \/ ens false=false; 0+0)))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # disj_elim ()
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2
  ───────────────────────────────────────────────────────────*
     ens a=true;
     (forall v.
        req x->v;
        ens x->v+1;
        (forall v1.
           req x->v1;
           ens x->v1+pow 2 (n-1+1)-2;
           (ens false=true; 1+1 \/ ens false=false; 1+0)))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # intro_pure "Ha"
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       (forall v1.
          req x->v1;
          ens x->v1+pow 2 (n-1+1)-2;
          (ens false=true; 1+1 \/ ens false=false; 1+0))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # forall_elim ["v+1+pow 2 (n-1+1)-2"]
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2
  ───────────────────────────────────────────────────────────*
     req x->v+1+pow 2 (n-1+1)-2;
     ens x->v+1+pow 2 (n-1+1)-2+1;
     (forall v1.
        req x->v1;
        ens x->v1+pow 2 (n-1+1)-2;
        (ens false=true; 1+1 \/ ens false=false; 1+0))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # elim_heap ()
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1+pow 2 (n-1+1)-2+1;
     (forall v1.
        req x->v1;
        ens x->v1+pow 2 (n-1+1)-2;
        (ens false=true; 1+1 \/ ens false=false; 1+0))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # intro_heap ()
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2+1
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+pow 2 (n-1+1)-2;
       (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # forall_elim ["v+1+pow 2 (n-1+1)-2+1"]
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2+1
  ───────────────────────────────────────────────────────────*
     req x->v+1+pow 2 (n-1+1)-2+1;
     ens x->v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2;
     (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # elim_heap ()
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2;
     (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # have ~name:"H_eq" "v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2 = v+pow 2 (n+1)-2"
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2=v+pow 2 (n+1)-2
  (2 more goals)
  
  
  # admit ()
  
  a, n, v, x
  H_eq: v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2=v+pow 2 (n+1)-2
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2;
     (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # rewrite "H_eq"
  
  a, n, v, x
  H_eq: v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2=v+pow 2 (n+1)-2
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+pow 2 (n+1)-2;
     (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # clear_pure "H_eq"
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+pow 2 (n+1)-2;
     (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # intro_heap ()
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+pow 2 (n+1)-2
  ───────────────────────────────────────────────────────────*
     ens false=true; 1+1 \/ ens false=false; 1+0
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  (1 more goals)
  
  
  # elim_heap ()
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens false=true; 1+1 \/ ens false=false; 1+0
  <: ens a=true; 1 \/ ens a=false; 0
  (1 more goals)
  
  
  # disj_elim ()
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens false=true; 1+1
  <: ens a=true; 1 \/ ens a=false; 0
  (2 more goals)
  
  
  # intro_pure "H_absurd"
  
  a, n, v, x
  H_absurd: false=true
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     1+1
  <: ens a=true; 1 \/ ens a=false; 0
  (2 more goals)
  
  
  # ex_falso ()
  
  a, n, v, x
  H_absurd: false=true
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  false
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens false=false; 1+0
  <: ens a=true; 1 \/ ens a=false; 0
  (1 more goals)
  
  
  # intro_pure "_"
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     1+0
  <: ens a=true; 1 \/ ens a=false; 0
  (1 more goals)
  
  
  # left ()
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     1+0
  <: ens a=true; 1
  (1 more goals)
  
  
  # elim_pure ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  a, n, v, x
  Ha: a=true
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     1+0
  <: 1
  (1 more goals)
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable v
  Warning, file line 0, characters 0-0: unused variable x
  ==> Valid
  
  
  a, n, v, x
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2
  ───────────────────────────────────────────────────────────*
     ens a=false;
     (forall v.
        req x->v;
        ens x->v+1;
        (forall v1.
           req x->v1;
           ens x->v1+pow 2 (n-1+1)-2;
           (ens false=true; 0+1 \/ ens false=false; 0+0)))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # intro_pure "Ha"
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       (forall v1.
          req x->v1;
          ens x->v1+pow 2 (n-1+1)-2;
          (ens false=true; 0+1 \/ ens false=false; 0+0))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # forall_elim ["v+1+pow 2 (n-1+1)-2"]
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2
  ───────────────────────────────────────────────────────────*
     req x->v+1+pow 2 (n-1+1)-2;
     ens x->v+1+pow 2 (n-1+1)-2+1;
     (forall v1.
        req x->v1;
        ens x->v1+pow 2 (n-1+1)-2;
        (ens false=true; 0+1 \/ ens false=false; 0+0))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # elim_heap ()
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1+pow 2 (n-1+1)-2+1;
     (forall v1.
        req x->v1;
        ens x->v1+pow 2 (n-1+1)-2;
        (ens false=true; 0+1 \/ ens false=false; 0+0))
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # intro_heap ()
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2+1
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+pow 2 (n-1+1)-2;
       (ens false=true; 0+1 \/ ens false=false; 0+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # forall_elim ["v+1+pow 2 (n-1+1)-2+1"]
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+1+pow 2 (n-1+1)-2+1
  ───────────────────────────────────────────────────────────*
     req x->v+1+pow 2 (n-1+1)-2+1;
     ens x->v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2;
     (ens false=true; 0+1 \/ ens false=false; 0+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # elim_heap ()
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2;
     (ens false=true; 0+1 \/ ens false=false; 0+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # have ~name:"H_eq" "v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2 = v+pow 2 (n+1)-2"
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2=v+pow 2 (n+1)-2
  (1 more goals)
  
  
  # admit ()
  
  a, n, v, x
  H_eq: v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2=v+pow 2 (n+1)-2
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2;
     (ens false=true; 0+1 \/ ens false=false; 0+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # rewrite "H_eq"
  
  a, n, v, x
  H_eq: v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2=v+pow 2 (n+1)-2
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+pow 2 (n+1)-2;
     (ens false=true; 0+1 \/ ens false=false; 0+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # clear_pure "H_eq"
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens x->v+pow 2 (n+1)-2;
     (ens false=true; 0+1 \/ ens false=false; 0+0)
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # intro_heap ()
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  x->v+pow 2 (n+1)-2
  ───────────────────────────────────────────────────────────*
     ens false=true; 0+1 \/ ens false=false; 0+0
  <: ens x->v+pow 2 (n+1)-2;
     (ens a=true; 1 \/ ens a=false; 0)
  
  
  # elim_heap ()
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens false=true; 0+1 \/ ens false=false; 0+0
  <: ens a=true; 1 \/ ens a=false; 0
  
  
  # disj_elim ()
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens false=true; 0+1
  <: ens a=true; 1 \/ ens a=false; 0
  (1 more goals)
  
  
  # intro_pure "H_absurd"
  
  a, n, v, x
  H_absurd: false=true
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     0+1
  <: ens a=true; 1 \/ ens a=false; 0
  (1 more goals)
  
  
  # ex_falso ()
  
  a, n, v, x
  H_absurd: false=true
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  false
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     ens false=false; 0+0
  <: ens a=true; 1 \/ ens a=false; 0
  
  
  # intro_pure "_"
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     0+0
  <: ens a=true; 1 \/ ens a=false; 0
  
  
  # right ()
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     0+0
  <: ens a=false; 0
  
  
  # elim_pure ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  a, n, v, x
  Ha: a=false
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          (forall a.
             reset
               (do_toss_n n1 x; r.
                  (ens (a /\ r)=true; 1
                   \/ ens (a /\ r)=false; 0)) <:
               (forall v.
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     0+0
  <: 0
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable v
  Warning, file line 0, characters 0-0: unused variable x
  ==> Valid
  
  no more goals
  
  # qed ()
  lemma do_toss_n_spec declared
  
  # lemma ~name:"toss_spec"
      {| forall x. toss x <: forall v. req x->v; ens x->v+2; 1 |}
  
  ────────────────────────────────────────────────────────────
  forall x. toss x <: (forall v. req x->v; ens x->v+2; 1)
  
  
  # forall_intro ()
  
  x
  ────────────────────────────────────────────────────────────
     toss x
  <: forall v. req x->v; ens x->v+2; 1
  
  
  # forall_intro ()
  
  v, x
  ────────────────────────────────────────────────────────────
     toss x
  <: req x->v; ens x->v+2; 1
  
  
  # intro_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     toss x
  <: ens x->v+2; 1
  
  
  # unfold "toss"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset (do_toss x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # unfold "do_toss"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (shift k
          (incr x; k true; r1. incr x; k false; r2. r1+r2);
          r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # unfold "incr"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (shift k
          ((forall v. req x->v; ens x->v+1);
           k true; r1.
             (forall v. req x->v; ens x->v+1);
             k false; r2. r1+r2); r.
          (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # shift_reset_reduce ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       reset
         ((fun r2 ->
            reset (ens r2=true; 1 \/ ens r2=false; 0)) true;
            r1.
            (forall v1. req x->v1; ens x->v1+1);
            (fun r3 ->
              reset (ens r3=true; 1 \/ ens r3=false; 0))
              false; r2. r1+r2)
  <: ens x->v+2; 1
  
  
  # simpl ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       reset
         (reset (ens true=true; 1 \/ ens true=false; 0); r1.
            (forall v1.
               req x->v1;
               ens x->v1+1;
               reset
                 (ens false=true; 1 \/ ens false=false; 0);
                 r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # forall_elim ["v"]
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     req x->v;
     ens x->v+1;
     reset
       (reset (ens true=true; 1 \/ ens true=false; 0); r1.
          (forall v1.
             req x->v1;
             ens x->v1+1;
             reset (ens false=true; 1 \/ ens false=false; 0);
               r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # elim_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
     ens x->v+1;
     reset
       (reset (ens true=true; 1 \/ ens true=false; 0); r1.
          (forall v1.
             req x->v1;
             ens x->v1+1;
             reset (ens false=true; 1 \/ ens false=false; 0);
               r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # intro_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       (reset (ens true=true; 1 \/ ens true=false; 0); r1.
          (forall v.
             req x->v;
             ens x->v+1;
             reset (ens false=true; 1 \/ ens false=false; 0);
               r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # shift_reset_reduce ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens true=true;
     (forall v.
        req x->v;
        ens x->v+1;
        (ens false=true; 1+1 \/ ens false=false; 1+0))
     \/ ens true=false;
        (forall v.
           req x->v;
           ens x->v+1;
           (ens false=true; 0+1 \/ ens false=false; 0+0))
  <: ens x->v+2; 1
  
  
  # disj_elim ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens true=true;
     (forall v.
        req x->v;
        ens x->v+1;
        (ens false=true; 1+1 \/ ens false=false; 1+0))
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # intro_pure "_"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # forall_elim ["v+1"]
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     req x->v+1;
     ens x->v+1+1;
     (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # elim_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
     ens x->v+1+1;
     (ens false=true; 1+1 \/ ens false=false; 1+0)
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # intro_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens false=true; 1+1 \/ ens false=false; 1+0
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # disj_elim ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens false=true; 1+1
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # intro_pure "H_absurd"
  
  v, x
  H_absurd: false=true
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     1+1
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # ex_falso ()
  
  v, x
  H_absurd: false=true
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
  false
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens false=false; 1+0
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # intro_pure "_"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     1+0
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # elim_heap ()
  Warning, file line 0, characters 0-0: unused variable x
  
  v, x
  ────────────────────────────────────────────────────────────
     1+0
  <: 1
  (1 more goals)
  
  
  # admit ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens true=false;
     (forall v.
        req x->v;
        ens x->v+1;
        (ens false=true; 0+1 \/ ens false=false; 0+0))
  <: ens x->v+2; 1
  
  
  # intro_pure "H_absurd"
  
  v, x
  H_absurd: true=false
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       (ens false=true; 0+1 \/ ens false=false; 0+0)
  <: ens x->v+2; 1
  
  
  # ex_falso ()
  
  v, x
  H_absurd: true=false
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
  false
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  no more goals
  
  # qed ()
  lemma toss_spec declared
  
  # lemma ~name:"toss_n_spec/1"
      {| forall x. toss_n 1 x <: forall v. req x->v; ens x->v+2; 1 |}
  
  ────────────────────────────────────────────────────────────
  forall x. toss_n 1 x <: (forall v. req x->v; ens x->v+2; 1)
  
  
  # forall_intro ()
  
  x
  ────────────────────────────────────────────────────────────
     toss_n 1 x
  <: forall v. req x->v; ens x->v+2; 1
  
  
  # forall_intro ()
  
  v, x
  ────────────────────────────────────────────────────────────
     toss_n 1 x
  <: req x->v; ens x->v+2; 1
  
  
  # intro_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     toss_n 1 x
  <: ens x->v+2; 1
  
  
  # unfold "toss_n"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n 1 x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # unfold "do_toss_n"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       ((ens 1=0; true
         \/ ens 1>0;
            do_toss x; r1. do_toss_n (1-1) x; r2. r1 /\ r2);
          r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # unfold "do_toss"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       ((ens 1=0; true
         \/ ens 1>0;
            shift k
              (incr x; k true; r2. incr x; k false; r3. r2+r3);
              r1. do_toss_n (1-1) x; r2. r1 /\ r2); r.
          (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # unfold "incr"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       ((ens 1=0; true
         \/ ens 1>0;
            shift k
              ((forall v. req x->v; ens x->v+1);
               k true; r2.
                 (forall v. req x->v; ens x->v+1);
                 k false; r3. r2+r3); r1.
              do_toss_n (1-1) x; r2. r1 /\ r2); r.
          (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # unfold "do_toss_n"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       ((ens 1=0; true
         \/ ens 1>0;
            shift k
              ((forall v. req x->v; ens x->v+1);
               k true; r2.
                 (forall v. req x->v; ens x->v+1);
                 k false; r3. r2+r3); r1.
              (ens 1-1=0; true
               \/ ens 1-1>0;
                  do_toss x; r3.
                    do_toss_n (1-1-1) x; r4. r3 /\ r4); r2.
                r1 /\ r2); r.
          (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # shift_reset_reduce ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens 1=0; (ens true=true; 1 \/ ens true=false; 0)
     \/ ens 1>0;
        (forall v.
           req x->v;
           ens x->v+1;
           reset
             ((fun r2 ->
                reset
                  (((ens 1-1=0; true
                     \/ ens 1-1>0;
                        do_toss x; r5.
                          do_toss_n (1-1-1) x; r6. r5 /\ r6);
                      r4. r2 /\ r4); r3.
                     (ens r3=true; 1 \/ ens r3=false; 0)))
                true; r1.
                (forall v1. req x->v1; ens x->v1+1);
                (fun r3 ->
                  reset
                    (((ens 1-1=0; true
                       \/ ens 1-1>0;
                          do_toss x; r6.
                            do_toss_n (1-1-1) x; r7. r6 /\ r7);
                        r5. r3 /\ r5); r4.
                       (ens r4=true; 1 \/ ens r4=false; 0)))
                  false; r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # disj_elim ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens 1=0; (ens true=true; 1 \/ ens true=false; 0)
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # intro_pure "H_absurd"
  
  v, x
  H_absurd: 1=0
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens true=true; 1 \/ ens true=false; 0
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # ex_falso ()
  
  v, x
  H_absurd: 1=0
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
  false
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens 1>0;
     (forall v.
        req x->v;
        ens x->v+1;
        reset
          ((fun r2 ->
             reset
               (((ens 1-1=0; true
                  \/ ens 1-1>0;
                     do_toss x; r5.
                       do_toss_n (1-1-1) x; r6. r5 /\ r6);
                   r4. r2 /\ r4); r3.
                  (ens r3=true; 1 \/ ens r3=false; 0))) true;
             r1.
             (forall v1. req x->v1; ens x->v1+1);
             (fun r3 ->
               reset
                 (((ens 1-1=0; true
                    \/ ens 1-1>0;
                       do_toss x; r6.
                         do_toss_n (1-1-1) x; r7. r6 /\ r7);
                     r5. r3 /\ r5); r4.
                    (ens r4=true; 1 \/ ens r4=false; 0)))
               false; r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # intro_pure "_"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       reset
         ((fun r2 ->
            reset
              (((ens 1-1=0; true
                 \/ ens 1-1>0;
                    do_toss x; r5.
                      do_toss_n (1-1-1) x; r6. r5 /\ r6); r4.
                  r2 /\ r4); r3.
                 (ens r3=true; 1 \/ ens r3=false; 0))) true;
            r1.
            (forall v1. req x->v1; ens x->v1+1);
            (fun r3 ->
              reset
                (((ens 1-1=0; true
                   \/ ens 1-1>0;
                      do_toss x; r6.
                        do_toss_n (1-1-1) x; r7. r6 /\ r7);
                    r5. r3 /\ r5); r4.
                   (ens r4=true; 1 \/ ens r4=false; 0)))
              false; r2. r1+r2)
  <: ens x->v+2; 1
  
  
  # forall_elim ["v"]
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     req x->v;
     ens x->v+1;
     reset
       ((fun r2 ->
          reset
            (((ens 1-1=0; true
               \/ ens 1-1>0;
                  do_toss x; r5.
                    do_toss_n (1-1-1) x; r6. r5 /\ r6); r4.
                r2 /\ r4); r3.
               (ens r3=true; 1 \/ ens r3=false; 0))) true;
          r1.
          (forall v1. req x->v1; ens x->v1+1);
          (fun r3 ->
            reset
              (((ens 1-1=0; true
                 \/ ens 1-1>0;
                    do_toss x; r6.
                      do_toss_n (1-1-1) x; r7. r6 /\ r7); r5.
                  r3 /\ r5); r4.
                 (ens r4=true; 1 \/ ens r4=false; 0))) false;
            r2. r1+r2)
  <: ens x->v+2; 1
  
  
  # elim_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
     ens x->v+1;
     reset
       ((fun r2 ->
          reset
            (((ens 1-1=0; true
               \/ ens 1-1>0;
                  do_toss x; r5.
                    do_toss_n (1-1-1) x; r6. r5 /\ r6); r4.
                r2 /\ r4); r3.
               (ens r3=true; 1 \/ ens r3=false; 0))) true;
          r1.
          (forall v1. req x->v1; ens x->v1+1);
          (fun r3 ->
            reset
              (((ens 1-1=0; true
                 \/ ens 1-1>0;
                    do_toss x; r6.
                      do_toss_n (1-1-1) x; r7. r6 /\ r7); r5.
                  r3 /\ r5); r4.
                 (ens r4=true; 1 \/ ens r4=false; 0))) false;
            r2. r1+r2)
  <: ens x->v+2; 1
  
  
  # intro_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       ((fun r2 ->
          reset
            (((ens 1-1=0; true
               \/ ens 1-1>0;
                  do_toss x; r5.
                    do_toss_n (1-1-1) x; r6. r5 /\ r6); r4.
                r2 /\ r4); r3.
               (ens r3=true; 1 \/ ens r3=false; 0))) true;
          r1.
          (forall v. req x->v; ens x->v+1);
          (fun r3 ->
            reset
              (((ens 1-1=0; true
                 \/ ens 1-1>0;
                    do_toss x; r6.
                      do_toss_n (1-1-1) x; r7. r6 /\ r7); r5.
                  r3 /\ r5); r4.
                 (ens r4=true; 1 \/ ens r4=false; 0))) false;
            r2. r1+r2)
  <: ens x->v+2; 1
  
  
  # simpl ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       (reset
          (ens 1-1=0;
           (ens (true /\ true)=true; 1
            \/ ens (true /\ true)=false; 0)
           \/ ens 1-1>0;
              do_toss x; r2.
                do_toss_n (1-1-1) x; r3.
                  (ens (true /\ (r2 /\ r3))=true; 1
                   \/ ens (true /\ (r2 /\ r3))=false; 0));
          r1.
          (forall v.
             req x->v;
             ens x->v+1;
             reset
               (ens 1-1=0;
                (ens (false /\ true)=true; 1
                 \/ ens (false /\ true)=false; 0)
                \/ ens 1-1>0;
                   do_toss x; r3.
                     do_toss_n (1-1-1) x; r4.
                       (ens (false /\ (r3 /\ r4))=true; 1
                        \/ ens (false /\ (r3 /\ r4))=false; 0));
               r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # shift_reset_reduce ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens 1-1=0;
     (ens (true /\ true)=true;
      (forall v.
         req x->v;
         ens x->v+1;
         (ens 1-1=0;
          (ens (false /\ true)=true; 1+1
           \/ ens (false /\ true)=false; 1+0)
          \/ ens 1-1>0;
             reset
               (do_toss x; r3.
                  do_toss_n (1-1-1) x; r4.
                    (ens (false /\ (r3 /\ r4))=true; 1
                     \/ ens (false /\ (r3 /\ r4))=false; 0));
               r2. 1+r2))
      \/ ens (true /\ true)=false;
         (forall v.
            req x->v;
            ens x->v+1;
            (ens 1-1=0;
             (ens (false /\ true)=true; 0+1
              \/ ens (false /\ true)=false; 0+0)
             \/ ens 1-1>0;
                reset
                  (do_toss x; r3.
                     do_toss_n (1-1-1) x; r4.
                       (ens (false /\ (r3 /\ r4))=true; 1
                        \/ ens (false /\ (r3 /\ r4))=false; 0));
                  r2. 0+r2)))
     \/ ens 1-1>0;
        reset
          (do_toss x; r2.
             do_toss_n (1-1-1) x; r3.
               (ens (true /\ (r2 /\ r3))=true; 1
                \/ ens (true /\ (r2 /\ r3))=false; 0)); r1.
          (forall v.
             req x->v;
             ens x->v+1;
             (ens 1-1=0;
              (ens (false /\ true)=true; r1+1
               \/ ens (false /\ true)=false; r1+0)
              \/ ens 1-1>0;
                 reset
                   (do_toss x; r3.
                      do_toss_n (1-1-1) x; r4.
                        (ens (false /\ (r3 /\ r4))=true; 1
                         \/ ens (false /\ (r3 /\ r4))=false;
                            0)); r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # disj_elim ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens 1-1=0;
     (ens (true /\ true)=true;
      (forall v.
         req x->v;
         ens x->v+1;
         (ens 1-1=0;
          (ens (false /\ true)=true; 1+1
           \/ ens (false /\ true)=false; 1+0)
          \/ ens 1-1>0;
             reset
               (do_toss x; r3.
                  do_toss_n (1-1-1) x; r4.
                    (ens (false /\ (r3 /\ r4))=true; 1
                     \/ ens (false /\ (r3 /\ r4))=false; 0));
               r2. 1+r2))
      \/ ens (true /\ true)=false;
         (forall v.
            req x->v;
            ens x->v+1;
            (ens 1-1=0;
             (ens (false /\ true)=true; 0+1
              \/ ens (false /\ true)=false; 0+0)
             \/ ens 1-1>0;
                reset
                  (do_toss x; r3.
                     do_toss_n (1-1-1) x; r4.
                       (ens (false /\ (r3 /\ r4))=true; 1
                        \/ ens (false /\ (r3 /\ r4))=false; 0));
                  r2. 0+r2)))
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # intro_pure "_"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens (true /\ true)=true;
     (forall v.
        req x->v;
        ens x->v+1;
        (ens 1-1=0;
         (ens (false /\ true)=true; 1+1
          \/ ens (false /\ true)=false; 1+0)
         \/ ens 1-1>0;
            reset
              (do_toss x; r3.
                 do_toss_n (1-1-1) x; r4.
                   (ens (false /\ (r3 /\ r4))=true; 1
                    \/ ens (false /\ (r3 /\ r4))=false; 0));
              r2. 1+r2))
     \/ ens (true /\ true)=false;
        (forall v.
           req x->v;
           ens x->v+1;
           (ens 1-1=0;
            (ens (false /\ true)=true; 0+1
             \/ ens (false /\ true)=false; 0+0)
            \/ ens 1-1>0;
               reset
                 (do_toss x; r3.
                    do_toss_n (1-1-1) x; r4.
                      (ens (false /\ (r3 /\ r4))=true; 1
                       \/ ens (false /\ (r3 /\ r4))=false; 0));
                 r2. 0+r2))
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # disj_elim ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens (true /\ true)=true;
     (forall v.
        req x->v;
        ens x->v+1;
        (ens 1-1=0;
         (ens (false /\ true)=true; 1+1
          \/ ens (false /\ true)=false; 1+0)
         \/ ens 1-1>0;
            reset
              (do_toss x; r3.
                 do_toss_n (1-1-1) x; r4.
                   (ens (false /\ (r3 /\ r4))=true; 1
                    \/ ens (false /\ (r3 /\ r4))=false; 0));
              r2. 1+r2))
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # intro_pure "_"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       (ens 1-1=0;
        (ens (false /\ true)=true; 1+1
         \/ ens (false /\ true)=false; 1+0)
        \/ ens 1-1>0;
           reset
             (do_toss x; r3.
                do_toss_n (1-1-1) x; r4.
                  (ens (false /\ (r3 /\ r4))=true; 1
                   \/ ens (false /\ (r3 /\ r4))=false; 0));
             r2. 1+r2)
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # forall_elim ["v+1"]
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     req x->v+1;
     ens x->v+1+1;
     (ens 1-1=0;
      (ens (false /\ true)=true; 1+1
       \/ ens (false /\ true)=false; 1+0)
      \/ ens 1-1>0;
         reset
           (do_toss x; r3.
              do_toss_n (1-1-1) x; r4.
                (ens (false /\ (r3 /\ r4))=true; 1
                 \/ ens (false /\ (r3 /\ r4))=false; 0)); r2.
           1+r2)
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # elim_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
     ens x->v+1+1;
     (ens 1-1=0;
      (ens (false /\ true)=true; 1+1
       \/ ens (false /\ true)=false; 1+0)
      \/ ens 1-1>0;
         reset
           (do_toss x; r3.
              do_toss_n (1-1-1) x; r4.
                (ens (false /\ (r3 /\ r4))=true; 1
                 \/ ens (false /\ (r3 /\ r4))=false; 0)); r2.
           1+r2)
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # intro_heap ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens 1-1=0;
     (ens (false /\ true)=true; 1+1
      \/ ens (false /\ true)=false; 1+0)
     \/ ens 1-1>0;
        reset
          (do_toss x; r3.
             do_toss_n (1-1-1) x; r4.
               (ens (false /\ (r3 /\ r4))=true; 1
                \/ ens (false /\ (r3 /\ r4))=false; 0)); r2.
          1+r2
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # disj_elim ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens 1-1=0;
     (ens (false /\ true)=true; 1+1
      \/ ens (false /\ true)=false; 1+0)
  <: ens x->v+2; 1
  (3 more goals)
  
  
  # intro_pure "_"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens (false /\ true)=true; 1+1
     \/ ens (false /\ true)=false; 1+0
  <: ens x->v+2; 1
  (3 more goals)
  
  
  # disj_elim ()
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens (false /\ true)=true; 1+1
  <: ens x->v+2; 1
  (4 more goals)
  
  
  # goal_is {| ens (false /\ true)=true; 1+1 <: ens x->v+2; 1 |}
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens (false /\ true)=true; 1+1
  <: ens x->v+2; 1
  (4 more goals)
  
  
  # rewrite "conj_false_l"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens false=true; 1+1
  <: ens x->v+2; 1
  (4 more goals)
  
  
  # intro_pure "H_absurd"
  
  v, x
  H_absurd: false=true
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     1+1
  <: ens x->v+2; 1
  (4 more goals)
  
  
  # ex_falso ()
  
  v, x
  H_absurd: false=true
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
  false
  (4 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens (false /\ true)=false; 1+0
  <: ens x->v+2; 1
  (3 more goals)
  
  
  # intro_pure "_"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     1+0
  <: ens x->v+2; 1
  (3 more goals)
  
  
  # elim_heap ()
  Warning, file line 0, characters 0-0: unused variable x
  
  v, x
  ────────────────────────────────────────────────────────────
     1+0
  <: 1
  (3 more goals)
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable v
  Warning, file line 0, characters 0-0: unused variable x
  ==> Valid
  
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     ens 1-1>0;
     reset
       (do_toss x; r3.
          do_toss_n (1-1-1) x; r4.
            (ens (false /\ (r3 /\ r4))=true; 1
             \/ ens (false /\ (r3 /\ r4))=false; 0)); r2.
       1+r2
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # intro_pure "H_absurd"
  
  v, x
  H_absurd: 1-1>0
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss x; r3.
          do_toss_n (1-1-1) x; r4.
            (ens (false /\ (r3 /\ r4))=true; 1
             \/ ens (false /\ (r3 /\ r4))=false; 0)); r2.
       1+r2
  <: ens x->v+2; 1
  (2 more goals)
  
  
  # ex_falso ()
  
  v, x
  H_absurd: 1-1>0
  ────────────────────────────────────────────────────────────
  x->v+1+1
  ───────────────────────────────────────────────────────────*
  false
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens (true /\ true)=false;
     (forall v.
        req x->v;
        ens x->v+1;
        (ens 1-1=0;
         (ens (false /\ true)=true; 0+1
          \/ ens (false /\ true)=false; 0+0)
         \/ ens 1-1>0;
            reset
              (do_toss x; r3.
                 do_toss_n (1-1-1) x; r4.
                   (ens (false /\ (r3 /\ r4))=true; 1
                    \/ ens (false /\ (r3 /\ r4))=false; 0));
              r2. 0+r2))
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # rewrite "conj_true_l"
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens true=false;
     (forall v.
        req x->v;
        ens x->v+1;
        (ens 1-1=0;
         (ens (false /\ true)=true; 0+1
          \/ ens (false /\ true)=false; 0+0)
         \/ ens 1-1>0;
            reset
              (do_toss x; r3.
                 do_toss_n (1-1-1) x; r4.
                   (ens (false /\ (r3 /\ r4))=true; 1
                    \/ ens (false /\ (r3 /\ r4))=false; 0));
              r2. 0+r2))
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # intro_pure "H_absurd"
  
  v, x
  H_absurd: true=false
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       (ens 1-1=0;
        (ens (false /\ true)=true; 0+1
         \/ ens (false /\ true)=false; 0+0)
        \/ ens 1-1>0;
           reset
             (do_toss x; r3.
                do_toss_n (1-1-1) x; r4.
                  (ens (false /\ (r3 /\ r4))=true; 1
                   \/ ens (false /\ (r3 /\ r4))=false; 0));
             r2. 0+r2)
  <: ens x->v+2; 1
  (1 more goals)
  
  
  # ex_falso ()
  
  v, x
  H_absurd: true=false
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
  false
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  
  v, x
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     ens 1-1>0;
     reset
       (do_toss x; r2.
          do_toss_n (1-1-1) x; r3.
            (ens (true /\ (r2 /\ r3))=true; 1
             \/ ens (true /\ (r2 /\ r3))=false; 0)); r1.
       (forall v.
          req x->v;
          ens x->v+1;
          (ens 1-1=0;
           (ens (false /\ true)=true; r1+1
            \/ ens (false /\ true)=false; r1+0)
           \/ ens 1-1>0;
              reset
                (do_toss x; r3.
                   do_toss_n (1-1-1) x; r4.
                     (ens (false /\ (r3 /\ r4))=true; 1
                      \/ ens (false /\ (r3 /\ r4))=false; 0));
                r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # intro_pure "H_absurd"
  
  v, x
  H_absurd: 1-1>0
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss x; r2.
          do_toss_n (1-1-1) x; r3.
            (ens (true /\ (r2 /\ r3))=true; 1
             \/ ens (true /\ (r2 /\ r3))=false; 0)); r1.
       (forall v.
          req x->v;
          ens x->v+1;
          (ens 1-1=0;
           (ens (false /\ true)=true; r1+1
            \/ ens (false /\ true)=false; r1+0)
           \/ ens 1-1>0;
              reset
                (do_toss x; r3.
                   do_toss_n (1-1-1) x; r4.
                     (ens (false /\ (r3 /\ r4))=true; 1
                      \/ ens (false /\ (r3 /\ r4))=false; 0));
                r2. r1+r2))
  <: ens x->v+2; 1
  
  
  # ex_falso ()
  
  v, x
  H_absurd: 1-1>0
  ────────────────────────────────────────────────────────────
  x->v+1
  ───────────────────────────────────────────────────────────*
  false
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  no more goals
  
  # qed ()
  lemma toss_n_spec/1 declared
  
  # lemma ~name:"toss_n_spec"
      {| forall n x. toss_n n x <: forall v. req x->v; ens x->v+pow 2 (n+1)-2; 1 |}
  
  ────────────────────────────────────────────────────────────
  forall n x.
    toss_n n x <:
      (forall v. req x->v; ens x->v+pow 2 (n+1)-2; 1)
  
  
  # forall_intro ()
  
  n, x
  ────────────────────────────────────────────────────────────
     toss_n n x
  <: forall v. req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # forall_intro ()
  
  n, v, x
  ────────────────────────────────────────────────────────────
     toss_n n x
  <: req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # intro_heap ()
  
  n, v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     toss_n n x
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # unfold "toss_n"
  
  n, v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # have ~name:"H_eq_true" {| forall r. ens r=true <: ens (true /\ r)=true |}
  
  n, v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
  forall r. ens r=true <: ens (true /\ r)=true
  (1 more goals)
  
  
  # forall_intro ()
  
  n, r, v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens r=true
  <: ens (true /\ r)=true
  (1 more goals)
  
  
  # rewrite "conj_true_l"
  
  n, r, v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens r=true
  <: ens r=true
  (1 more goals)
  
  
  # refl ()
  
  n, v, x
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # have ~name:"H_eq_false"
      {| forall r. ens r=false <: ens (true /\ r)=false |}
  
  n, v, x
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
  forall r. ens r=false <: ens (true /\ r)=false
  (1 more goals)
  
  
  # forall_intro ()
  
  n, r, v, x
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens r=false
  <: ens (true /\ r)=false
  (1 more goals)
  
  
  # rewrite "conj_true_l"
  
  n, r, v, x
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     ens r=false
  <: ens r=false
  (1 more goals)
  
  
  # refl ()
  
  n, v, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # rewrite "H_eq_true"
  
  n, v, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n n x; r.
          (ens (true /\ r)=true; 1 \/ ens r=false; 0))
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # rewrite "H_eq_false"
  
  n, v, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset
       (do_toss_n n x; r.
          (ens (true /\ r)=true; 1
           \/ ens (true /\ r)=false; 0))
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # rewrite "do_toss_n_spec"
  
  n, v, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens true=true; 1 \/ ens true=false; 0)
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # clear_pure "H_eq_true"
  
  n, v, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens true=true; 1 \/ ens true=false; 0)
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # clear_pure "H_eq_false"
  
  n, v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens true=true; 1 \/ ens true=false; 0)
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # forall_elim ["v"]
  
  n, v, x
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     req x->v;
     ens x->v+pow 2 (n+1)-2;
     (ens true=true; 1 \/ ens true=false; 0)
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # elim_heap ()
  
  n, v, x
  ────────────────────────────────────────────────────────────
     ens x->v+pow 2 (n+1)-2;
     (ens true=true; 1 \/ ens true=false; 0)
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # intro_heap ()
  
  n, v, x
  ────────────────────────────────────────────────────────────
  x->v+pow 2 (n+1)-2
  ───────────────────────────────────────────────────────────*
     ens true=true; 1 \/ ens true=false; 0
  <: ens x->v+pow 2 (n+1)-2; 1
  
  
  # elim_heap ()
  
  n, v, x
  ────────────────────────────────────────────────────────────
     ens true=true; 1 \/ ens true=false; 0
  <: 1
  
  
  # disj_elim ()
  
  n, v, x
  ────────────────────────────────────────────────────────────
     ens true=true; 1
  <: 1
  (1 more goals)
  
  
  # intro_pure "_"
  
  n, v, x
  ────────────────────────────────────────────────────────────
     1
  <: 1
  (1 more goals)
  
  
  # refl ()
  
  n, v, x
  ────────────────────────────────────────────────────────────
     ens true=false; 0
  <: 1
  
  
  # intro_pure "H_absurd"
  
  n, v, x
  H_absurd: true=false
  ────────────────────────────────────────────────────────────
     0
  <: 1
  
  
  # ex_falso ()
  
  n, v, x
  H_absurd: true=false
  ────────────────────────────────────────────────────────────
  false
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable v
  Warning, file line 0, characters 0-0: unused variable n
  no more goals
  
  # qed ()
  lemma toss_n_spec declared
  
  # Options.fail_fast := false


