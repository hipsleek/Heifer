
  $ ./equiv.exe
  
  # declare
      {| loop2 x y z = forall a.
    (req z->a /\ a>0; ens z->a; incr y x; decr z 1; loop2 x y z) /\
    (req z->a /\ a<=0; ens z->a)
    |}
  loop2 declared
  
  # declare {| ds1 y z = ens y->0 * z->2*.x; loop2 x y z; read y |}
  ds1 declared
  
  # declare {| ds2 y z = ens y->0 * z->x; loop2 x y z; read y; r. r*.2 |}
  ds2 declared
  
  # start_proof
      {| forall x y z.
       loop2 x y z
    <: forall a b. req is_nat b; req y->a * z->b; ens y->(a+b*.x) * z->0
  |}
  
  ────────────────────────────────────────────────────────────
  forall x y z.
    loop2 x y z <:
      (forall a b.
         req is_nat b; req y->a * z->b; ens y->a+b*.x * z->0)
  
  
  # forall_intro ()
  
  x, y, z
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: forall a b.
       req is_nat b; req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # forall_intro ()
  
  a, b, x, y, z
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req is_nat b; req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # intro_pure "Htyb"
  
  a, b, x, y, z
  Htyb: is_nat b
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # revert "a"
  
  b, x, y, z
  Htyb: is_nat b
  ────────────────────────────────────────────────────────────
  forall a.
    loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # induction ~name:"IH" (`Int 0) "b"
  
  b, x, y, z
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  forall a.
    loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0
  
  
  # forall_intro ()
  
  a1, b, x, y, z
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # goal_is {|
       loop2 x y z
    <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  |}
  
  a1, b, x, y, z
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     loop2 x y z
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # unfold "loop2"
  
  a1, b, x, y, z
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     forall a.
       (req z->a /\ a>0;
        ens z->a; incr y x; decr z 1; loop2 x y z) /\
         (req z->a /\ a<=0; ens z->a)
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # goal_is
      {| forall a.
         (req z->a /\ a>0;
          ens z->a; incr y x; decr z 1; loop2 x y z) /\
           (req z->a /\ a<=0; ens z->a)
    <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  |}
  error: goal was expected to be
    forall a2.
      (req z->a2 /\ a2>0; ens z->a2; incr y x; decr z 1; loop2 x y z) /\
        (req z->a2 /\ a2<=0; ens z->a2) <:
        req y->a1 * z->b; ens y->a1+b*.x * z->0
  but was:
    (forall a2.
       (req z->a2 /\ a2>0; ens z->a2; incr y x; decr z 1; loop2 x y z) /\
         (req z->a2 /\ a2<=0; ens z->a2)) <:
      req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  # forall_elim ["b"]
  
  a1, b, x, y, z
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     (req z->b /\ b>0;
      ens z->b; incr y x; decr z 1; loop2 x y z) /\
       (req z->b /\ b<=0; ens z->b)
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # case ~name:"Hb" "b > 0"
  
  a1, b, x, y, z
  Hb: b>0
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     (req z->b /\ b>0;
      ens z->b; incr y x; decr z 1; loop2 x y z) /\
       (req z->b /\ b<=0; ens z->b)
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # conj_elim_l ()
  
  a1, b, x, y, z
  Hb: b>0
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     req z->b /\ b>0;
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # goal_is
      {|
       req z->b /\ b>0;
       ens z->b; incr y x; decr z 1; loop2 x y z
    <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  |}
  
  a1, b, x, y, z
  Hb: b>0
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     req z->b /\ b>0;
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_intro ()
  
  a1, b, x, y, z
  Hb: b>0
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  z->b
  ───────────────────────────────────────────────────────────*
     req z->b /\ b>0;
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # axiom ~name:"Hh" {| forall p q. req p /\ q <: req p; req q |}
  
  a1, b, x, y, z
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  z->b
  ───────────────────────────────────────────────────────────*
     req z->b /\ b>0;
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "Hh"
  
  a1, b, x, y, z
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  z->b
  ───────────────────────────────────────────────────────────*
     (req z->b; req b>0);
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # simpl ()
  
  a1, b, x, y, z
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  z->b
  ───────────────────────────────────────────────────────────*
     req z->b;
     req b>0; ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_elim ()
  
  a1, b, x, y, z
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  ───────────────────────────────────────────────────────────*
     req b>0; ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable a1
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable z
  ==> Valid
  
  
  a1, b, x, y, z
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  ───────────────────────────────────────────────────────────*
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # revert_heap ()
  
  a1, b, x, y, z
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a1; ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # axiom ~name:"H_ens_swap" {| forall p q. ens p; ens q <: ens q; ens p |}
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a1; ens z->b; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "H_ens_swap"
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     (ens z->b; ens y->a1); incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # simpl ()
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens z->b; ens y->a1; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # axiom ~name:"Hincr" {| forall x y v. ens x->v; incr x y <: ens x->v+y |}
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens z->b; ens y->a1; incr y x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "Hincr"
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens z->b; ens y->a1+x; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "H_ens_swap"
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     (ens y->a1+x; ens z->b); decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # simpl ()
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a1+x; ens z->b; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # axiom ~name:"Hdecr" {| forall x y v. ens x->v; decr x y <: ens x->v-y |}
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a1+x; ens z->b; decr z 1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "Hdecr"
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a1+x; ens z->b-1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # goal_is
      {|
       ens y->a1+x; ens z->b-1; loop2 x y z
    <: ens y->a1+b*.x * z->0
  |}
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a1+x; ens z->b-1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # intro_heap ()
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1+x
  ───────────────────────────────────────────────────────────*
     ens z->b-1; loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # intro_heap ()
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a1+x
  ───────────────────────────────────────────────────────────*
     loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # specialize "IH" ["b-1"; "a1+x"]
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: b-1>=0 /\ b-1<b =>
        loop2 x y z <:
          req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a1+x
  ───────────────────────────────────────────────────────────*
     loop2 x y z
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # rewrite "IH"
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: b-1>=0 /\ b-1<b =>
        loop2 x y z <:
          req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a1+x
  ───────────────────────────────────────────────────────────*
  b-1>=0 /\ b-1<b
  (2 more goals)
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable a1
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable z
  ==> Valid
  
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: b-1>=0 /\ b-1<b =>
        loop2 x y z <:
          req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a1+x
  ───────────────────────────────────────────────────────────*
     req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # goal_is
      {|
       req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
    <: ens y->a1+b*.x * z->0
  |}
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: b-1>=0 /\ b-1<b =>
        loop2 x y z <:
          req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b-1
  y->a1+x
  ───────────────────────────────────────────────────────────*
     req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # req_heap_elim ()
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: b-1>=0 /\ b-1<b =>
        loop2 x y z <:
          req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
     ens y->a1+x+(b-1)*.x * z->0
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # ens_heap_elim ()
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: b-1>=0 /\ b-1<b =>
        loop2 x y z <:
          req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1+x+(b-1)*.x
  z->0
  ───────────────────────────────────────────────────────────*
     ()
  <: ens y->a1+b*.x * z->0
  (1 more goals)
  
  
  # ens_heap_intro ()
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  
  a1, b, x, y, z
  H_ens_swap: forall p q. ens p; ens q <: ens q; ens p
  Hb: b>0
  Hdecr: forall x y v. ens x->v; decr x y <: ens x->v-y
  Hh: forall p q. req p /\ q <: req p; req q
  Hincr: forall x y v. ens x->v; incr x y <: ens x->v+y
  Htyb: is_nat b
  IH: b-1>=0 /\ b-1<b =>
        loop2 x y z <:
          req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  ────────────────────────────────────────────────────────────
     ()
  <: ()
  (1 more goals)
  
  
  # Options.show_why3_goal := true
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall a1 : term, b : term, x : term, y : term, z : term.
        ((gt b (TInt 0)) = (TBool true))
          ->
          (b.is_nat)
          ->
          (TUnit = TUnit)
  end
  Warning, file line 0, characters 0-0: unused variable a1
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable z
  module M
    use Heifer
    goal goal1 : true
  end
  ==> Valid
  
  
  a1, b, x, y, z
  Hb: !b>0
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     (req z->b /\ b>0;
      ens z->b; incr y x; decr z 1; loop2 x y z) /\
       (req z->b /\ b<=0; ens z->b)
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # conj_elim_r ()
  
  a1, b, x, y, z
  Hb: !b>0
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     req z->b /\ b<=0; ens z->b
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # goal_is
      {|
       req z->b /\ b<=0; ens z->b
    <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  |}
  
  a1, b, x, y, z
  Hb: !b>0
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     req z->b /\ b<=0; ens z->b
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # axiom ~name:"Hh" {| forall p q. req p /\ q <: req p; req q |}
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     req z->b /\ b<=0; ens z->b
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # rewrite "Hh"
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     (req z->b; req b<=0); ens z->b
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # simpl ()
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     req z->b; req b<=0; ens z->b
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
  
  
  # req_heap_intro ()
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  z->b
  ───────────────────────────────────────────────────────────*
     req z->b; req b<=0; ens z->b
  <: ens y->a1+b*.x * z->0
  
  
  # req_heap_elim ()
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  ───────────────────────────────────────────────────────────*
     req b<=0; ens z->b
  <: ens y->a1+b*.x * z->0
  
  
  # Options.show_why3_goal := true
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall a1 : term, b : term, x : term, y : term, z : term.
        (not ((gt b (TInt 0)) = (TBool true)))
          ->
          (b.is_nat)
          ->
          ((le b (TInt 0)) = (TBool true))
  end
  Warning, file line 0, characters 0-0: unused variable a1
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable z
  module M
    use Heifer
    constant b : term
    axiom H : not gt b (TInt 0) = TBool True
    axiom H1 : is_nat b
    goal goal1 : le b (TInt 0) = TBool True
  end
  ==> Valid
  
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  y->a1
  ───────────────────────────────────────────────────────────*
     ens z->b
  <: ens y->a1+b*.x * z->0
  
  
  # ens_heap_elim ()
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
  z->b
  y->a1
  ───────────────────────────────────────────────────────────*
     ()
  <: ens y->a1+b*.x * z->0
  
  
  # ens_heap_intro ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall z : term, y : term, x : term, b : term, a1 : term.
        (b.is_nat)
          ->
          (not ((gt b (TInt 0)) = (TBool true)))
          ->
          ((plus a1 (times b x)) = a1)
  end
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  module M
    use Heifer
    constant x : term
    constant b : term
    constant a1 : term
    axiom H : is_nat b
    axiom H1 :
      not match (b, TInt 0) with
          | TInt a11, TInt b1 -> TBool (if a11 > b1 then True else False)
          | _ -> TErr
          end = TBool True
    goal goal1 : plus a1 (times b x) = a1
  end
  module M
    use heifer.Heifer
    
    goal goal1:
      forall z : term, y : term, x : term, b : term, a1 : term.
        (b.is_nat)
          ->
          (not ((gt b (TInt 0)) = (TBool true)))
          ->
          ((TInt 0) = b)
  end
  Warning, file line 0, characters 0-0: unused variable z
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable a1
  module M
    use Heifer
    constant b : term
    axiom H : is_nat b
    axiom H1 :
      not match (b, TInt 0) with
          | TInt a1, TInt b1 -> TBool (if a1 > b1 then True else False)
          | _ -> TErr
          end = TBool True
    goal goal1 : TInt 0 = b
  end
  
  a1, b, x, y, z
  Hb: !b>0
  Hh: forall p q. req p /\ q <: req p; req q
  Htyb: is_nat b
  IH: forall b1 a1.
        b1>=0 /\ b1<b =>
          loop2 x y z <:
            req y->a1 * z->b1; ens y->a1+b1*.x * z->0
  ────────────────────────────────────────────────────────────
     ()
  <: ()
  
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall a1 : term, b : term, x : term, y : term, z : term.
        (not ((gt b (TInt 0)) = (TBool true)))
          ->
          (b.is_nat)
          ->
          (TUnit = TUnit)
  end
  Warning, file line 0, characters 0-0: unused variable a1
  Warning, file line 0, characters 0-0: unused variable x
  Warning, file line 0, characters 0-0: unused variable y
  Warning, file line 0, characters 0-0: unused variable z
  module M
    use Heifer
    goal goal1 : true
  end
  ==> Valid
  
  no more goals
  
  # qed ()
  no more goals
