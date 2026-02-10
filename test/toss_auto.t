
  $ ./toss_auto.exe
  
  # Options.fail_fast := true
  
  # axiom ~name:"conj_false_l" {| forall t. (false /\ t) = false |}
  axiom conj_false_l declared
  
  # axiom ~name:"conj_false_r" {| forall t. (t /\ false) = false |}
  axiom conj_false_r declared
  
  # axiom ~name:"conj_true_l" {| forall t. (true /\ t) = t |}
  axiom conj_true_l declared
  
  # axiom ~name:"conj_true_r" {| forall t. (t /\ true) = t |}
  axiom conj_true_r declared
  
  # axiom ~name:"conj_assoc"
      {| forall t1 t2 t3. (t1 /\ (t2 /\ t3)) = ((t1 /\ t2) /\ t3) |}
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
  
  # lemma ~name:"toss_spec"
      {| forall x. toss x <: forall v. req is_int v; req x->v; ens x->v+2; 1 |}
  
  ────────────────────────────────────────────────────────────
  forall x.
    toss x <:
      (forall v. req is_int v; req x->v; ens x->v+2; 1)
  
  
  # forall_intro ()
  
  x
  ────────────────────────────────────────────────────────────
     toss x
  <: forall v. req is_int v; req x->v; ens x->v+2; 1
  
  
  # forall_intro ()
  
  v, x
  ────────────────────────────────────────────────────────────
     toss x
  <: req is_int v; req x->v; ens x->v+2; 1
  
  
  # intro_pure "Hv"
  
  v, x
  Hv: is_int v
  ────────────────────────────────────────────────────────────
     toss x
  <: req x->v; ens x->v+2; 1
  
  
  # intro_heap ()
  
  v, x
  Hv: is_int v
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     toss x
  <: ens x->v+2; 1
  
  
  # unfold "toss"
  
  v, x
  Hv: is_int v
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     reset (do_toss x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: ens x->v+2; 1
  
  
  # unfold "do_toss"
  
  v, x
  Hv: is_int v
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
  Hv: is_int v
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
  Hv: is_int v
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
  Hv: is_int v
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
  
  
  # shift_reset_reduce ()
  
  v, x
  Hv: is_int v
  ────────────────────────────────────────────────────────────
  x->v
  ───────────────────────────────────────────────────────────*
     forall v.
       req x->v;
       ens x->v+1;
       (ens true=true;
        (forall v1.
           req x->v1;
           ens x->v1+1;
           (ens false=true; 1+1 \/ ens false=false; 1+0))
        \/ ens true=false;
           (forall v1.
              req x->v1;
              ens x->v1+1;
              (ens false=true; 0+1 \/ ens false=false; 0+0)))
  <: ens x->v+2; 1
  
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  no more goals
  
  # Format.printf "%a@." Prover.Automation.pp_cert (Option.get c)
  forall_elim ["v"];
  elim_heap ();
  intro_heap ();
  disj_elim ();
  ( intro_pure "H";
    forall_elim ["v+1"];
    elim_heap ();
    intro_heap ();
    disj_elim ();
    ( intro_pure "H0";
      elim_heap ();
      prove () (* 1+1 <: 1 *) )
    ( intro_pure "H0";
      elim_heap ();
      prove () (* 1+0 <: 1 *) ) )
  ( intro_pure "H";
    forall_elim ["v+1"];
    elim_heap ();
    intro_heap ();
    disj_elim ();
    ( intro_pure "H0";
      elim_heap ();
      prove () (* 0+1 <: 1 *) )
    ( intro_pure "H0";
      elim_heap ();
      prove () (* 0+0 <: 1 *) ) )
  
  # qed ()
  lemma toss_spec declared
  
  # lemma ~name:"do_toss_n_spec"
      {|
      forall n x a.
        reset (do_toss_n n x; r. (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
        forall v. req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; (ens a=true; 1 \/ ens a=false; 0)
    |}
  
  ────────────────────────────────────────────────────────────
  forall n x a.
    reset
      (do_toss_n n x; r.
         (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      (forall v.
         req is_int v;
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
       req is_int v;
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
         req is_int v;
         req x->v;
         ens x->v+pow 2 (n+1)-2;
         (ens a=true; 1 \/ ens a=false; 0))
  
  
  # goal_is
      {|
      forall a.
        reset (do_toss_n n x; r. (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
        (forall v. req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; (ens a=true; 1 \/ ens a=false; 0))
    |}
  
  n, x
  ────────────────────────────────────────────────────────────
  forall a.
    reset
      (do_toss_n n x; r.
         (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      (forall v.
         req is_int v;
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
                  req is_int v;
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
  forall a.
    reset
      (do_toss_n n x; r.
         (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      (forall v.
         req is_int v;
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
                  req is_int v;
                  req x->v;
                  ens x->v+pow 2 (n1+1)-2;
                  (ens a=true; 1 \/ ens a=false; 0)))
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r.
          (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0))
  <: forall v.
       req is_int v;
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
                  req is_int v;
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
       req is_int v;
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
                  req is_int v;
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
       req is_int v;
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
                  req is_int v;
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
       req is_int v;
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
                  req is_int v;
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
       req is_int v;
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
                  req is_int v;
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
       req is_int v;
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
                  req is_int v;
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
       req is_int v;
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens a=true; 1 \/ ens a=false; 0)
  
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable x
  no more goals
  
  # Format.printf "%a@." Prover.Automation.pp_cert (Option.get c)
  disj_elim ();
  ( forall_intro ();
    intro_pure "H";
    disj_elim ();
    ( intro_pure "H0";
      intro_pure "H1";
      intro_heap ();
      elim_heap ();
      left ();
      elim_pure ();
      refl (); )
    ( intro_pure "H0";
      intro_pure "H1";
      intro_heap ();
      elim_heap ();
      right ();
      elim_pure ();
      refl (); ) )
  ( forall_intro ();
    intro_pure "H";
    intro_pure "H0";
    intro_heap ();
    forall_elim ["v"];
    elim_heap ();
    intro_heap ();
    rewrite "conj_assoc" (* forall t1 t2 t3.
                              (t1 /\ (t2 /\ t3))=(t1 /\ t2 /\
                                                    t3) *);
    rewrite "IH" (* forall n1.
                      n1>=0 /\ n1<n =>
                        (forall a.
                           reset
                             (do_toss_n n1 x; r.
                                (ens (a /\ r)=true; 1
                                 \/ ens (a /\ r)=false; 0)) <:
                             (forall v.
                                req is_int v;
                                req x->v;
                                ens x->v+pow 2 (n1+1)-2;
                                (ens a=true; 1
                                 \/ ens a=false; 0))) *);
    ( prove () (* n-1>=0 /\ n-1<n *) )
    forall_elim ["v+1"];
    elim_pure ();
    elim_heap ();
    intro_heap ();
    disj_elim ();
    ( intro_pure "H1";
      forall_elim ["v+1+pow 2 (n-1+1)-2"];
      elim_heap ();
      intro_heap ();
      rewrite "IH" (* forall n1.
                        n1>=0 /\ n1<n =>
                          (forall a.
                             reset
                               (do_toss_n n1 x; r.
                                  (ens (a /\ r)=true; 1
                                   \/ ens (a /\ r)=false; 0)) <:
                               (forall v.
                                  req is_int v;
                                  req x->v;
                                  ens x->v+pow 2 (n1+1)-2;
                                  (ens a=true; 1
                                   \/ ens a=false; 0))) *);
      ( prove () (* n-1>=0 /\ n-1<n *) )
      forall_elim ["v+1+pow 2 (n-1+1)-2+1"];
      elim_pure ();
      elim_heap ();
      intro_heap ();
      disj_elim ();
      ( intro_pure "H2";
        elim_heap ();
        left ();
        elim_pure ();
        prove () (* 1+1 <: 1 *) )
      ( intro_pure "H2";
        elim_heap ();
        left ();
        elim_pure ();
        prove () (* 1+0 <: 1 *) ) )
    ( intro_pure "H1";
      forall_elim ["v+1+pow 2 (n-1+1)-2"];
      elim_heap ();
      intro_heap ();
      rewrite "IH" (* forall n1.
                        n1>=0 /\ n1<n =>
                          (forall a.
                             reset
                               (do_toss_n n1 x; r.
                                  (ens (a /\ r)=true; 1
                                   \/ ens (a /\ r)=false; 0)) <:
                               (forall v.
                                  req is_int v;
                                  req x->v;
                                  ens x->v+pow 2 (n1+1)-2;
                                  (ens a=true; 1
                                   \/ ens a=false; 0))) *);
      ( prove () (* n-1>=0 /\ n-1<n *) )
      forall_elim ["v+1+pow 2 (n-1+1)-2+1"];
      elim_pure ();
      elim_heap ();
      intro_heap ();
      disj_elim ();
      ( intro_pure "H2";
        elim_heap ();
        left ();
        elim_pure ();
        prove () (* 0+1 <: 1 *) )
      ( intro_pure "H2";
        elim_heap ();
        right ();
        elim_pure ();
        prove () (* 0+0 <: 0 *) ) ) )
  
  # qed ()
  lemma do_toss_n_spec declared
  
  # lemma ~name:"toss_n_spec"
      {| forall n x. toss_n n x <: forall v. req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1 |}
  
  ────────────────────────────────────────────────────────────
  forall n x.
    toss_n n x <:
      (forall v.
         req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1)
  
  
  # forall_intro ()
  
  n, x
  ────────────────────────────────────────────────────────────
     toss_n n x
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # unfold "toss_n"
  
  n, x
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # have ~name:"H_eq_true" {| forall r. ens r=true <: ens (true /\ r)=true |}
  
  n, x
  ────────────────────────────────────────────────────────────
  forall r. ens r=true <: ens (true /\ r)=true
  (1 more goals)
  
  
  # simple ()
  Warning, file line 0, characters 0-0: unused variable n
  Warning, file line 0, characters 0-0: unused variable x
  
  n, x
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # have ~name:"H_eq_false"
      {| forall r. ens r=false <: ens (true /\ r)=false |}
  
  n, x
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
  forall r. ens r=false <: ens (true /\ r)=false
  (1 more goals)
  
  
  # simple ()
  Warning, file line 0, characters 0-0: unused variable n
  Warning, file line 0, characters 0-0: unused variable x
  
  n, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0))
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # rewrite "H_eq_true"
  
  n, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r.
          (ens (true /\ r)=true; 1 \/ ens r=false; 0))
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # rewrite "H_eq_false"
  
  n, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  H_eq_true: forall r. ens r=true <: ens (true /\ r)=true
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r.
          (ens (true /\ r)=true; 1
           \/ ens (true /\ r)=false; 0))
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # clear_pure "H_eq_true"
  
  n, x
  H_eq_false: forall r. ens r=false <: ens (true /\ r)=false
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r.
          (ens (true /\ r)=true; 1
           \/ ens (true /\ r)=false; 0))
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # clear_pure "H_eq_false"
  
  n, x
  ────────────────────────────────────────────────────────────
     reset
       (do_toss_n n x; r.
          (ens (true /\ r)=true; 1
           \/ ens (true /\ r)=false; 0))
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  
  # rewrite "do_toss_n_spec"
  
  n, x
  ────────────────────────────────────────────────────────────
     forall v.
       req is_int v;
       req x->v;
       ens x->v+pow 2 (n+1)-2;
       (ens true=true; 1 \/ ens true=false; 0)
  <: forall v.
       req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1
  
  Warning, file line 0, characters 0-0: unused variable n
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable n
  Warning, file line 0, characters 0-0: unused variable x
  no more goals
  
  # Format.printf "%a@." Prover.Automation.pp_cert (Option.get c)
  forall_intro ();
  intro_pure "H";
  intro_heap ();
  forall_elim ["v"];
  elim_pure ();
  elim_heap ();
  intro_heap ();
  disj_elim ();
  ( intro_pure "H0";
    elim_heap ();
    refl (); )
  ( intro_pure "H0";
    elim_heap ();
    prove () (* 0 <: 1 *) )
  
  # qed ()
  lemma toss_n_spec declared
  
  # Options.fail_fast := false
