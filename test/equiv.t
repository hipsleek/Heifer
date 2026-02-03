
  $ ./equiv.exe
  
  # Options.fail_fast := true
  
  # declare
      {|
      loop2 x y z =
        forall a.
          (req z->a /\ a>0; ens z->a; incr y x; decr z 1; loop2 x y z) /\
          (req z->a /\ a<=0; ens z->a)
    |}
  loop2 declared
  
  # axiom ~name:"incr_spec"
      {| forall l x. incr l x <: forall v. req l->v; ens l->v+x |}
  axiom incr_spec declared
  
  # axiom ~name:"decr_spec"
      {| forall l x. decr l x <: forall v. req l->v; ens l->v-x |}
  axiom decr_spec declared
  
  # start_proof
      {|
      forall x y z.
        loop2 x y z <: forall a b. req b>=0; req y->a * z->b; ens y->(a+b*.x) * z->0
  |}
  
  ────────────────────────────────────────────────────────────
  forall x y z.
    loop2 x y z <:
      (forall a b.
         req b>=0; req y->a * z->b; ens y->a+b*.x * z->0)
  
  
  # forall_intro ()
  
  x, y, z
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: forall a b.
       req b>=0; req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # forall_intro ()
  
  a, b, x, y, z
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req b>=0; req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # intro_pure "Hb"
  
  a, b, x, y, z
  Hb: b>=0
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # revert "a"
  
  b, x, y, z
  Hb: b>=0
  ────────────────────────────────────────────────────────────
  forall a.
    loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # goal_is
      {| forall a. loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0 |}
  
  b, x, y, z
  Hb: b>=0
  ────────────────────────────────────────────────────────────
  forall a.
    loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # induction ~name:"IH" (`Int 0) "b"
  
  b, x, y, z
  Hb: b>=0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  forall a.
    loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # forall_intro ()
  
  a, b, x, y, z
  Hb: b>=0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # goal_is {| loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0 |}
  
  a, b, x, y, z
  Hb: b>=0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # unfold "loop2"
  
  a, b, x, y, z
  Hb: b>=0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     forall a.
       (req z->a /\ a>0;
        ens z->a; incr y x; decr z 1; loop2 x y z) /\
         (req z->a /\ a<=0; ens z->a)
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # forall_elim ["b"]
  
  a, b, x, y, z
  Hb: b>=0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     (req z->b /\ b>0;
      ens z->b; incr y x; decr z 1; loop2 x y z) /\
       (req z->b /\ b<=0; ens z->b)
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # case ~name:"Hb_gt" "b > 0"
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     (req z->b /\ b>0;
      ens z->b; incr y x; decr z 1; loop2 x y z) /\
       (req z->b /\ b<=0; ens z->b)
  <: req y->a * z->b; ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # conj_elim_l ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req z->b /\ b>0;
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # goal_is
      {|
         req z->b /\ b>0; ens z->b; incr y x; decr z 1; loop2 x y z
      <: req y->a * z->b; ens y->a+b*.x * z->0
    |}
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req z->b /\ b>0;
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # unmix ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req b>0;
     req z->b; ens z->b; incr y x; decr z 1; loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # req_pure_elim ()
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req z->b; ens z->b; incr y x; decr z 1; loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_intro ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a
  z->b
  ───────────────────────────────────────────────────────────*
     req z->b; ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a
  ───────────────────────────────────────────────────────────*
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # ens_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b
  y->a
  ───────────────────────────────────────────────────────────*
     incr y x; decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "incr_spec"
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b
  y->a
  ───────────────────────────────────────────────────────────*
     (forall v. req y->v; ens y->v+x); decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # forall_elim ["a"]
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b
  y->a
  ───────────────────────────────────────────────────────────*
     (req y->a; ens y->a+x); decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # simpl ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b
  y->a
  ───────────────────────────────────────────────────────────*
     req y->a; ens y->a+x; decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b
  ───────────────────────────────────────────────────────────*
     ens y->a+x; decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # ens_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a+x
  z->b
  ───────────────────────────────────────────────────────────*
     decr z 1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "decr_spec"
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a+x
  z->b
  ───────────────────────────────────────────────────────────*
     (forall v. req z->v; ens z->v-1); loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # forall_elim ["b"]
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a+x
  z->b
  ───────────────────────────────────────────────────────────*
     (req z->b; ens z->b-1); loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # simpl ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a+x
  z->b
  ───────────────────────────────────────────────────────────*
     req z->b; ens z->b-1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a+x
  ───────────────────────────────────────────────────────────*
     ens z->b-1; loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # ens_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
     loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # specialize "IH" ["b-1"]
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: b-1>=0 /\ b-1<b =>
        b-1>=0 =>
          (forall a.
             loop2 x y z <:
               req y->a * z->b-1; ens y->a+(b-1)*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
     loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # forward "IH"
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: b-1>=0 /\ b-1<b =>
        b-1>=0 =>
          (forall a.
             loop2 x y z <:
               req y->a * z->b-1; ens y->a+(b-1)*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
  b-1>=0 /\ b-1<b
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: b-1>=0 =>
        (forall a.
           loop2 x y z <:
             req y->a * z->b-1; ens y->a+(b-1)*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
     loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # forward "IH"
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: b-1>=0 =>
        (forall a.
           loop2 x y z <:
             req y->a * z->b-1; ens y->a+(b-1)*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
  b-1>=0
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: forall a.
        loop2 x y z <:
          req y->a * z->b-1; ens y->a+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
     loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # specialize "IH" ["a+x"]
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: loop2 x y z <:
        req y->a+x * z->b-1; ens y->a+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
     loop2 x y z
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "IH"
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: loop2 x y z <:
        req y->a+x * z->b-1; ens y->a+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a+x
  ───────────────────────────────────────────────────────────*
     req y->a+x * z->b-1; ens y->a+x+(b-1)*.x * z->0
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: loop2 x y z <:
        req y->a+x * z->b-1; ens y->a+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a+x+(b-1)*.x * z->0
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # ens_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: loop2 x y z <:
        req y->a+x * z->b-1; ens y->a+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a+x+(b-1)*.x
  z->0
  ───────────────────────────────────────────────────────────*
     ()
  <: ens y->a+b*.x * z->0
  (1 more goals)
  
  
  # ens_heap_intro ()
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: b>0
  IH: loop2 x y z <:
        req y->a+x * z->b-1; ens y->a+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
     ()
  <: ()
  (1 more goals)
  
  
  # refl ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     (req z->b /\ b>0;
      ens z->b; incr y x; decr z 1; loop2 x y z) /\
       (req z->b /\ b<=0; ens z->b)
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # conj_elim_r ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req z->b /\ b<=0; ens z->b
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # goal_is
      {|
         req z->b /\ b<=0; ens z->b
      <: req y->a * z->b; ens y->a+b*.x * z->0
    |}
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req z->b /\ b<=0; ens z->b
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # unmix ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req b<=0; req z->b; ens z->b
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # req_pure_elim ()
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     req z->b; ens z->b
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # req_heap_intro ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a
  z->b
  ───────────────────────────────────────────────────────────*
     req z->b; ens z->b
  <: ens y->a+b*.x * z->0
  
  
  # req_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  y->a
  ───────────────────────────────────────────────────────────*
     ens z->b
  <: ens y->a+b*.x * z->0
  
  
  # ens_heap_elim ()
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
  z->b
  y->a
  ───────────────────────────────────────────────────────────*
     ()
  <: ens y->a+b*.x * z->0
  
  
  # ens_heap_intro ()
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a
  
  a, b, x, y, z
  Hb: b>=0
  Hb_gt: !b>0
  IH: forall b1.
        b1>=0 /\ b1<b =>
          b1>=0 =>
            (forall a.
               loop2 x y z <:
                 req y->a * z->b1; ens y->a+b1*.x * z->0)
  ────────────────────────────────────────────────────────────
     ()
  <: ()
  
  
  # refl ()
  no more goals
  
  # qed ()
  
  # Options.fail_fast := false
