
  $ ./regex.exe
  
  # Options.fail_fast := true
  
  # axiom ~name:"eta_reduce" {| forall f. (fun x -> f x) <: f |}
  axiom eta_reduce declared
  
  # axiom ~name:"reset_under_bind"
      {| forall f1 f2. reset (f1; r. f2 r) <: reset (f1; r. reset (f2 r)) |}
  axiom reset_under_bind declared
  
  # axiom ~name:"double_reset" {| forall f. reset (reset (f)) <: reset (f) |}
  axiom double_reset declared
  
  # axiom ~name:"reset_over_disj"
      {| forall f1 f2. reset (f1 \/ f2) <: reset (f1) \/ reset (f2) |}
  axiom reset_over_disj declared
  
  # declare
      {|
    matches_prefix_sr r ns =
        (ens r=TREmp; Some ns)
      \/ (ex a. ens r=(TRAtom a); ((ex b ns1. ens ns=b::ns1 /\ a=b; Some ns1) \/ None))
      \/ (ex r1 r2. ens r=(TRSeq r1 r2);
                matches_prefix_sr r1 ns; v.
                  ((ens v=None; None)
                  \/ (ex rest. ens v=(Some rest); matches_prefix_sr r2 rest)))
      \/ (ex r1 r2. ens r=(TRDisj r1 r2);
                shift k
                  (matches_prefix_sr r1 ns; v1. k v1; r3.
                      ((ens r3=None; matches_prefix_sr r2 ns; a. k a)
                      \/ (ex a. ens r3=(Some a); r3))))
  |}
  matches_prefix_sr declared
  
  # declare
      {|
    matches_prefix_cps r ns k =
        ens r=TREmp; k (Some ns)
      \/ (ex a. ens r=(TRAtom a); ((ex b ns1. ens ns=b::ns1 /\ a=b; k (Some ns1)) \/ k None))
      \/ (ex r1 r2. ens r=(TRSeq r1 r2);
                matches_prefix_cps r1 ns (fun v ->
                  ens v=None; k(None)
                  \/ ex rest. ens v=(Some rest); matches_prefix_cps r2 rest k))
      \/ ex r1 r2. ens r=(TRDisj r1 r2);
                matches_prefix_cps r1 ns k; r3.
                ((ens r3=None; matches_prefix_cps r2 ns k) \/ r3)
  |}
  matches_prefix_cps declared
  
  # Options.show_why3_goal := true;
    start_proof
      {|
    forall r ns k.
      (forall r. reset (k r) <: k r) =>
      reset (matches_prefix_sr r ns; r1. k r1)
      <: matches_prefix_cps r ns k
  |}
  
  ────────────────────────────────────────────────────────────
  forall r ns k.
    (forall r1. reset (k r1) <: k r1) =>
      reset (matches_prefix_sr r ns; r1. k r1) <:
        matches_prefix_cps r ns k
  
  
  # forall_intro ()
  
  k, ns, r
  ────────────────────────────────────────────────────────────
  (forall r1. reset (k r1) <: k r1) =>
    reset (matches_prefix_sr r ns; r1. k r1) <:
      matches_prefix_cps r ns k
  
  
  # revert "k"
  
  ns, r
  ────────────────────────────────────────────────────────────
  forall k.
    (forall r1. reset (k r1) <: k r1) =>
      reset (matches_prefix_sr r ns; r1. k r1) <:
        matches_prefix_cps r ns k
  
  
  # revert "ns"
  
  r
  ────────────────────────────────────────────────────────────
  forall ns.
    (forall k.
       (forall r1. reset (k r1) <: k r1) =>
         reset (matches_prefix_sr r ns; r1. k r1) <:
           matches_prefix_cps r ns k)
  
  
  # induction ~name:"IH" `Regex "r"
  
  r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall ns.
    (forall k.
       (forall r1. reset (k r1) <: k r1) =>
         reset (matches_prefix_sr r ns; r1. k r1) <:
           matches_prefix_cps r ns k)
  
  
  # forall_intro ()
  
  ns, r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall k.
    (forall r1. reset (k r1) <: k r1) =>
      reset (matches_prefix_sr r ns; r1. k r1) <:
        matches_prefix_cps r ns k
  
  
  # forall_intro ()
  
  k, ns, r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  (forall r1. reset (k r1) <: k r1) =>
    reset (matches_prefix_sr r ns; r1. k r1) <:
      matches_prefix_cps r ns k
  
  
  # intro_pure "Hksf"
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (matches_prefix_sr r ns; r1. k r1)
  <: matches_prefix_cps r ns k
  
  
  # unfold "matches_prefix_cps"
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (matches_prefix_sr r ns; r1. k r1)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  
  
  # unfold "matches_prefix_sr"
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       ((ens r=TREmp; Some ns
         \/ (ex a.
               ens r=TRAtom a;
               ((ex b ns1. ens ns=b::ns1 /\ a=b; Some ns1)
                \/ None))
         \/ (ex r2 r3.
               ens r=TRSeq r2 r3;
               matches_prefix_sr r2 ns; v.
                 (ens v=None; None
                  \/ (ex rest.
                        ens v=Some rest;
                        matches_prefix_sr r3 rest)))
         \/ (ex r2 r3.
               ens r=TRDisj r2 r3;
               shift k1
                 (matches_prefix_sr r2 ns; v1.
                    k1 v1; r4.
                      (ens r4=None;
                       matches_prefix_sr r3 ns; a. k1 a
                       \/ (ex a. ens r4=Some a; r4))))); r1.
          k r1)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  
  
  # simpl ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ens r=TREmp; k Some ns
        \/ (ex a.
              ens r=TRAtom a;
              ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
               \/ k None))
        \/ (ex r1 r2.
              ens r=TRSeq r1 r2;
              matches_prefix_sr r1 ns; v.
                (ens v=None; k None
                 \/ (ex rest.
                       ens v=Some rest;
                       matches_prefix_sr r2 rest; r3. k r3)))
        \/ (ex r1 r2.
              ens r=TRDisj r1 r2;
              shift k1
                (matches_prefix_sr r1 ns; v1.
                   k1 v1; r4.
                     (ens r4=None;
                      matches_prefix_sr r2 ns; a. k1 a
                      \/ (ex a. ens r4=Some a; r4))); r3.
                k r3))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  
  
  # rewrite "reset_over_disj"
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ens r=TREmp; k Some ns
        \/ (ex a.
              ens r=TRAtom a;
              ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
               \/ k None))
        \/ (ex r1 r2.
              ens r=TRSeq r1 r2;
              matches_prefix_sr r1 ns; v.
                (ens v=None; k None
                 \/ (ex rest.
                       ens v=Some rest;
                       matches_prefix_sr r2 rest; r3. k r3))))
     \/ reset
          (ex r1 r2.
             ens r=TRDisj r1 r2;
             shift k1
               (matches_prefix_sr r1 ns; v1.
                  k1 v1; r4.
                    (ens r4=None;
                     matches_prefix_sr r2 ns; a. k1 a
                     \/ (ex a. ens r4=Some a; r4))); r3. 
               k r3)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  
  
  # rewrite "reset_over_disj"
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ens r=TREmp; k Some ns
        \/ (ex a.
              ens r=TRAtom a;
              ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
               \/ k None)))
     \/ reset
          (ex r1 r2.
             ens r=TRSeq r1 r2;
             matches_prefix_sr r1 ns; v.
               (ens v=None; k None
                \/ (ex rest.
                      ens v=Some rest;
                      matches_prefix_sr r2 rest; r3. k r3)))
     \/ reset
          (ex r1 r2.
             ens r=TRDisj r1 r2;
             shift k1
               (matches_prefix_sr r1 ns; v1.
                  k1 v1; r4.
                    (ens r4=None;
                     matches_prefix_sr r2 ns; a. k1 a
                     \/ (ex a. ens r4=Some a; r4))); r3. 
               k r3)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  
  
  # rewrite "reset_over_disj"
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
     \/ reset
          (ex a.
             ens r=TRAtom a;
             ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
              \/ k None))
     \/ reset
          (ex r1 r2.
             ens r=TRSeq r1 r2;
             matches_prefix_sr r1 ns; v.
               (ens v=None; k None
                \/ (ex rest.
                      ens v=Some rest;
                      matches_prefix_sr r2 rest; r3. k r3)))
     \/ reset
          (ex r1 r2.
             ens r=TRDisj r1 r2;
             shift k1
               (matches_prefix_sr r1 ns; v1.
                  k1 v1; r4.
                    (ens r4=None;
                     matches_prefix_sr r2 ns; a. k1 a
                     \/ (ex a. ens r4=Some a; r4))); r3. 
               k r3)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  
  
  # disj_elim ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
     \/ reset
          (ex a.
             ens r=TRAtom a;
             ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
              \/ k None))
     \/ reset
          (ex r1 r2.
             ens r=TRSeq r1 r2;
             matches_prefix_sr r1 ns; v.
               (ens v=None; k None
                \/ (ex rest.
                      ens v=Some rest;
                      matches_prefix_sr r2 rest; r3. k r3)))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  (1 more goals)
  
  
  # disj_elim ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
     \/ reset
          (ex a.
             ens r=TRAtom a;
             ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
              \/ k None))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  (2 more goals)
  
  
  # disj_elim ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  (3 more goals)
  
  
  # left ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
  (3 more goals)
  
  
  # left ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
  (3 more goals)
  
  
  # left ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
  <: ens r=TREmp; k Some ns
  (3 more goals)
  
  
  # goal_is
      {|
     reset (ens r=TREmp; k (Some ns))
  <: ens r=TREmp; k (Some ns)
  |}
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (ens r=TREmp; k Some ns)
  <: ens r=TREmp; k Some ns
  (3 more goals)
  
  
  # shift_reset_reduce ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TREmp; reset (k Some ns)
  <: ens r=TREmp; k Some ns
  (3 more goals)
  
  
  # rewrite "Hksf"
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TREmp; k Some ns
  <: ens r=TREmp; k Some ns
  (3 more goals)
  
  
  # refl ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex a.
          ens r=TRAtom a;
          ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
           \/ k None))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  (2 more goals)
  
  
  # left ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex a.
          ens r=TRAtom a;
          ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
           \/ k None))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
  (2 more goals)
  
  
  # left ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex a.
          ens r=TRAtom a;
          ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
           \/ k None))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
  (2 more goals)
  
  
  # right ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex a.
          ens r=TRAtom a;
          ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
           \/ k None))
  <: ex a.
       ens r=TRAtom a;
       ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
        \/ k None)
  (2 more goals)
  
  
  # goal_is
      {|
     reset (ex a.
       ens r=TRAtom a;
       ((ex b ns1. ens ns=b::ns1 /\ a=b; k (Some ns1)) \/ k None))
  <: (ex a.
       ens r=TRAtom a;
       ((ex b ns1. ens ns=b::ns1 /\ a=b; k (Some ns1)) \/ k None))
  |}
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex a.
          ens r=TRAtom a;
          ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
           \/ k None))
  <: ex a.
       ens r=TRAtom a;
       ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
        \/ k None)
  (2 more goals)
  
  
  # shift_reset_reduce ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex a.
       ens r=TRAtom a;
       ((ex b ns1. ens ns=b::ns1 /\ a=b; reset (k Some ns1))
        \/ reset (k None))
  <: ex a.
       ens r=TRAtom a;
       ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
        \/ k None)
  (2 more goals)
  
  
  # exists_elim ()
  
  a, k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TRAtom a;
     ((ex b ns1. ens ns=b::ns1 /\ a=b; reset (k Some ns1))
      \/ reset (k None))
  <: ex a.
       ens r=TRAtom a;
       ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
        \/ k None)
  (2 more goals)
  
  
  # exists_intro ["a"]
  
  a, k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TRAtom a;
     ((ex b ns1. ens ns=b::ns1 /\ a=b; reset (k Some ns1))
      \/ reset (k None))
  <: ens r=TRAtom a;
     ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1) \/ k None)
  (2 more goals)
  
  
  # rewrite "Hksf"
  
  a, k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TRAtom a;
     ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1) \/ k None)
  <: ens r=TRAtom a;
     ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1) \/ k None)
  (2 more goals)
  
  
  # refl ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex r1 r2.
          ens r=TRSeq r1 r2;
          matches_prefix_sr r1 ns; v.
            (ens v=None; k None
             \/ (ex rest.
                   ens v=Some rest;
                   matches_prefix_sr r2 rest; r3. k r3)))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  (1 more goals)
  
  
  # left ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex r1 r2.
          ens r=TRSeq r1 r2;
          matches_prefix_sr r1 ns; v.
            (ens v=None; k None
             \/ (ex rest.
                   ens v=Some rest;
                   matches_prefix_sr r2 rest; r3. k r3)))
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
  (1 more goals)
  
  
  # right ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex r1 r2.
          ens r=TRSeq r1 r2;
          matches_prefix_sr r1 ns; v.
            (ens v=None; k None
             \/ (ex rest.
                   ens v=Some rest;
                   matches_prefix_sr r2 rest; r3. k r3)))
  <: ex r1 r2.
       ens r=TRSeq r1 r2;
       matches_prefix_cps r1 ns
         (fun v ->
           ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # goal_is
      {|
    reset
      (ex r1 r2.
         ens r=TRSeq r1 r2;
         matches_prefix_sr r1 ns; v.
           (ens v=None; k None
            \/ (ex rest. ens v=Some rest; matches_prefix_sr r2 rest; r3. k r3))) <:
      (ex r1 r2.
         ens r=TRSeq r1 r2;
         matches_prefix_cps r1 ns
           (fun v ->
             ens v=None; k None
             \/ (ex rest. ens v=Some rest; matches_prefix_cps r2 rest k)))
  |}
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex r1 r2.
          ens r=TRSeq r1 r2;
          matches_prefix_sr r1 ns; v.
            (ens v=None; k None
             \/ (ex rest.
                   ens v=Some rest;
                   matches_prefix_sr r2 rest; r3. k r3)))
  <: ex r1 r2.
       ens r=TRSeq r1 r2;
       matches_prefix_cps r1 ns
         (fun v ->
           ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # shift_reset_reduce ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex r1 r2.
       ens r=TRSeq r1 r2;
       reset
         (matches_prefix_sr r1 ns; v.
            (ens v=None; k None
             \/ (ex rest.
                   ens v=Some rest;
                   matches_prefix_sr r2 rest; r3. k r3)))
  <: ex r1 r2.
       ens r=TRSeq r1 r2;
       matches_prefix_cps r1 ns
         (fun v ->
           ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # exists_elim ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TRSeq r1 r2;
     reset
       (matches_prefix_sr r1 ns; v.
          (ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_sr r2 rest; r3. k r3)))
  <: ex r1 r2.
       ens r=TRSeq r1 r2;
       matches_prefix_cps r1 ns
         (fun v ->
           ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # exists_intro ["r1"; "r2"]
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TRSeq r1 r2;
     reset
       (matches_prefix_sr r1 ns; v.
          (ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_sr r2 rest; r3. k r3)))
  <: ens r=TRSeq r1 r2;
     matches_prefix_cps r1 ns
       (fun v ->
         ens v=None; k None
         \/ (ex rest.
               ens v=Some rest; matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # ens_pure_elim "Hr"
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (matches_prefix_sr r1 ns; v.
          (ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_sr r2 rest; r3. k r3)))
  <: ens r=TRSeq r1 r2;
     matches_prefix_cps r1 ns
       (fun v ->
         ens v=None; k None
         \/ (ex rest.
               ens v=Some rest; matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # ens_pure_intro ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall k : term, ns : term, r : term, r1 : term, r2 : term.
        (r = (TRSeq r1 r2)) -> (r = (TRSeq r1 r2))
  end
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ns
  module M
    use Heifer
    goal goal1 : true
  end
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (matches_prefix_sr r1 ns; v.
          (ens v=None; k None
           \/ (ex rest.
                 ens v=Some rest;
                 matches_prefix_sr r2 rest; r3. k r3)))
  <: matches_prefix_cps r1 ns
       (fun v ->
         ens v=None; k None
         \/ (ex rest.
               ens v=Some rest; matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # rewrite "reset_under_bind"
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (matches_prefix_sr r1 ns; r3.
          reset
            ((fun r4 ->
               ens r4=None; k None
               \/ (ex rest.
                     ens r4=Some rest;
                     matches_prefix_sr r2 rest; r5. k r5)) r3))
  <: matches_prefix_cps r1 ns
       (fun v ->
         ens v=None; k None
         \/ (ex rest.
               ens v=Some rest; matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # rewrite "IH"
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  subregex r1 r
  (3 more goals)
  
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall k : term, ns : term, r : term, r1 : term, r2 : term.
        (r = (TRSeq r1 r2)) -> (subregex r1 r)
  end
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ns
  module M
    use Heifer
    constant r1 : term
    constant r2 : term
    goal goal1 : subregex r1 (TRSeq r1 r2)
  end
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall r3.
    reset
      ((fun r4 ->
         reset
           ((fun r5 ->
              ens r5=None; k None
              \/ (ex rest.
                    ens r5=Some rest;
                    matches_prefix_sr r2 rest; r6. k r6)) r4))
         r3) <:
      (fun r4 ->
        reset
          ((fun r5 ->
             ens r5=None; k None
             \/ (ex rest.
                   ens r5=Some rest;
                   matches_prefix_sr r2 rest; r6. k r6)) r4))
        r3
  (2 more goals)
  
  
  # simpl ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall r3.
    reset
      (reset
         (ens r3=None; k None
          \/ (ex rest.
                ens r3=Some rest;
                matches_prefix_sr r2 rest; r4. k r4))) <:
      reset
        (ens r3=None; k None
         \/ (ex rest.
               ens r3=Some rest;
               matches_prefix_sr r2 rest; r4. k r4))
  (2 more goals)
  
  
  # shift_reset_reduce ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall r3.
    ens r3=None; reset (k None)
    \/ (ex rest.
          ens r3=Some rest;
          reset (matches_prefix_sr r2 rest; r4. k r4)) <:
      ens r3=None; reset (k None)
      \/ (ex rest.
            ens r3=Some rest;
            reset (matches_prefix_sr r2 rest; r4. k r4))
  (2 more goals)
  
  
  # forall_intro ()
  
  k, ns, r, r0, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r0=None; reset (k None)
     \/ (ex rest.
           ens r0=Some rest;
           reset (matches_prefix_sr r2 rest; r3. k r3))
  <: ens r0=None; reset (k None)
     \/ (ex rest.
           ens r0=Some rest;
           reset (matches_prefix_sr r2 rest; r3. k r3))
  (2 more goals)
  
  
  # refl ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     matches_prefix_cps r1 ns
       (fun r3 ->
         reset
           ((fun r4 ->
              ens r4=None; k None
              \/ (ex rest.
                    ens r4=Some rest;
                    matches_prefix_sr r2 rest; r5. k r5)) r3))
  <: matches_prefix_cps r1 ns
       (fun v ->
         ens v=None; k None
         \/ (ex rest.
               ens v=Some rest; matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # simpl ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     matches_prefix_cps r1 ns
       (fun r3 ->
         reset
           (ens r3=None; k None
            \/ (ex rest.
                  ens r3=Some rest;
                  matches_prefix_sr r2 rest; r4. k r4)))
  <: matches_prefix_cps r1 ns
       (fun v ->
         ens v=None; k None
         \/ (ex rest.
               ens v=Some rest; matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # congruence ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     (fun r3 ->
       reset
         (ens r3=None; k None
          \/ (ex rest.
                ens r3=Some rest;
                matches_prefix_sr r2 rest; r4. k r4)))
  <: (fun v ->
       ens v=None; k None
       \/ (ex rest.
             ens v=Some rest; matches_prefix_cps r2 rest k))
  (1 more goals)
  
  
  # funext ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall x.
    (fun r3 ->
      reset
        (ens r3=None; k None
         \/ (ex rest.
               ens r3=Some rest;
               matches_prefix_sr r2 rest; r4. k r4))) x <:
      (fun v ->
        ens v=None; k None
        \/ (ex rest.
              ens v=Some rest; matches_prefix_cps r2 rest k))
        x
  (1 more goals)
  
  
  # forall_intro ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     (fun r3 ->
       reset
         (ens r3=None; k None
          \/ (ex rest.
                ens r3=Some rest;
                matches_prefix_sr r2 rest; r4. k r4))) x0
  <: (fun v ->
       ens v=None; k None
       \/ (ex rest.
             ens v=Some rest; matches_prefix_cps r2 rest k))
       x0
  (1 more goals)
  
  
  # simpl ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ens x0=None; k None
        \/ (ex rest.
              ens x0=Some rest;
              matches_prefix_sr r2 rest; r3. k r3))
  <: ens x0=None; k None
     \/ (ex rest.
           ens x0=Some rest; matches_prefix_cps r2 rest k)
  (1 more goals)
  
  
  # shift_reset_reduce ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x0=None; reset (k None)
     \/ (ex rest.
           ens x0=Some rest;
           reset (matches_prefix_sr r2 rest; r3. k r3))
  <: ens x0=None; k None
     \/ (ex rest.
           ens x0=Some rest; matches_prefix_cps r2 rest k)
  (1 more goals)
  
  
  # goal_is
      {|
     ens x0=None; reset (k None)
     \/ (ex rest.
           ens x0=Some rest; reset (matches_prefix_sr r2 rest; r3. k r3))
  <: ens x0=None; k None
     \/ (ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k)
  |}
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x0=None; reset (k None)
     \/ (ex rest.
           ens x0=Some rest;
           reset (matches_prefix_sr r2 rest; r3. k r3))
  <: ens x0=None; k None
     \/ (ex rest.
           ens x0=Some rest; matches_prefix_cps r2 rest k)
  (1 more goals)
  
  
  # congruence ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex rest.
       ens x0=Some rest;
       reset (matches_prefix_sr r2 rest; r3. k r3)
  <: ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k
  (2 more goals)
  
  
  # goal_is
      {|
     (ex rest. ens x0=Some rest; reset (matches_prefix_sr r2 rest; r3. k r3))
  <: ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k
  |}
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex rest.
       ens x0=Some rest;
       reset (matches_prefix_sr r2 rest; r3. k r3)
  <: ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k
  (2 more goals)
  
  
  # rewrite "IH"
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  subregex r2 r
  (4 more goals)
  
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall k : term, ns : term, r : term, r1 : term, r2 : term, x0 : term.
        (r = (TRSeq r1 r2)) -> (subregex r2 r)
  end
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ns
  Warning, file line 0, characters 0-0: unused variable x0
  module M
    use Heifer
    constant r1 : term
    constant r2 : term
    goal goal1 : subregex r2 (TRSeq r1 r2)
  end
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall r. reset (k r) <: k r
  (3 more goals)
  
  
  # forall_intro ()
  
  k, ns, r, r0, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (k r0)
  <: k r0
  (3 more goals)
  
  
  # rewrite "Hksf"
  
  k, ns, r, r0, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     k r0
  <: k r0
  (3 more goals)
  
  
  # refl ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k
  <: ex rest. ens x0=Some rest; matches_prefix_cps r2 rest k
  (2 more goals)
  
  
  # refl ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x0=None; reset (k None)
  <: ens x0=None; k None
  (1 more goals)
  
  
  # goal_is {|
     ens x0=None; reset (k None)
  <: ens x0=None; k None
  |}
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x0=None; reset (k None)
  <: ens x0=None; k None
  (1 more goals)
  
  
  # rewrite "Hksf"
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRSeq r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x0=None; k None
  <: ens x0=None; k None
  (1 more goals)
  
  
  # refl ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex r1 r2.
          ens r=TRDisj r1 r2;
          shift k1
            (matches_prefix_sr r1 ns; v1.
               k1 v1; r4.
                 (ens r4=None;
                  matches_prefix_sr r2 ns; a. k1 a
                  \/ (ex a. ens r4=Some a; r4))); r3. 
            k r3)
  <: ens r=TREmp; k Some ns
     \/ (ex a.
           ens r=TRAtom a;
           ((ex b ns1. ens ns=b::ns1 /\ a=b; k Some ns1)
            \/ k None))
     \/ (ex r1 r2.
           ens r=TRSeq r1 r2;
           matches_prefix_cps r1 ns
             (fun v ->
               ens v=None; k None
               \/ (ex rest.
                     ens v=Some rest;
                     matches_prefix_cps r2 rest k)))
     \/ (ex r1 r2.
           ens r=TRDisj r1 r2;
           matches_prefix_cps r1 ns k; r3.
             (ens r3=None; matches_prefix_cps r2 ns k \/ r3))
  
  
  # right ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex r1 r2.
          ens r=TRDisj r1 r2;
          shift k1
            (matches_prefix_sr r1 ns; v1.
               k1 v1; r4.
                 (ens r4=None;
                  matches_prefix_sr r2 ns; a. k1 a
                  \/ (ex a. ens r4=Some a; r4))); r3. 
            k r3)
  <: ex r1 r2.
       ens r=TRDisj r1 r2;
       matches_prefix_cps r1 ns k; r3.
         (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # goal_is
      {|
     reset
       (ex r1 r2.
          ens r=TRDisj r1 r2;
          shift k1
            (matches_prefix_sr r1 ns; v1.
               k1 v1; r4.
                 (ens r4=None; matches_prefix_sr r2 ns; a. k1 a
                  \/ (ex a. ens r4=Some a; r4))); r3.
            k r3)
  <: ex r1 r2.
       ens r=TRDisj r1 r2;
       matches_prefix_cps r1 ns k; r3.
         (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  |}
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (ex r1 r2.
          ens r=TRDisj r1 r2;
          shift k1
            (matches_prefix_sr r1 ns; v1.
               k1 v1; r4.
                 (ens r4=None;
                  matches_prefix_sr r2 ns; a. k1 a
                  \/ (ex a. ens r4=Some a; r4))); r3. 
            k r3)
  <: ex r1 r2.
       ens r=TRDisj r1 r2;
       matches_prefix_cps r1 ns k; r3.
         (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # shift_reset_reduce ()
  
  k, ns, r
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex r1 r2.
       ens r=TRDisj r1 r2;
       reset
         (matches_prefix_sr r1 ns; v1.
            (fun r4 -> reset (k r4)) v1; r3.
              (ens r3=None;
               matches_prefix_sr r2 ns; a.
                 (fun r4 -> reset (k r4)) a
               \/ (ex a. ens r3=Some a; r3)))
  <: ex r1 r2.
       ens r=TRDisj r1 r2;
       matches_prefix_cps r1 ns k; r3.
         (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # exists_elim ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TRDisj r1 r2;
     reset
       (matches_prefix_sr r1 ns; v1.
          (fun r4 -> reset (k r4)) v1; r3.
            (ens r3=None;
             matches_prefix_sr r2 ns; a.
               (fun r4 -> reset (k r4)) a
             \/ (ex a. ens r3=Some a; r3)))
  <: ex r1 r2.
       ens r=TRDisj r1 r2;
       matches_prefix_cps r1 ns k; r3.
         (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # exists_intro ["r1"; "r2"]
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens r=TRDisj r1 r2;
     reset
       (matches_prefix_sr r1 ns; v1.
          (fun r4 -> reset (k r4)) v1; r3.
            (ens r3=None;
             matches_prefix_sr r2 ns; a.
               (fun r4 -> reset (k r4)) a
             \/ (ex a. ens r3=Some a; r3)))
  <: ens r=TRDisj r1 r2;
     matches_prefix_cps r1 ns k; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # ens_pure_elim "Hr"
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (matches_prefix_sr r1 ns; v1.
          (fun r4 -> reset (k r4)) v1; r3.
            (ens r3=None;
             matches_prefix_sr r2 ns; a.
               (fun r4 -> reset (k r4)) a
             \/ (ex a. ens r3=Some a; r3)))
  <: ens r=TRDisj r1 r2;
     matches_prefix_cps r1 ns k; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # ens_pure_intro ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall k : term, ns : term, r : term, r1 : term, r2 : term.
        (r = (TRDisj r1 r2)) -> (r = (TRDisj r1 r2))
  end
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ns
  module M
    use Heifer
    goal goal1 : true
  end
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (matches_prefix_sr r1 ns; v1.
          (fun r4 -> reset (k r4)) v1; r3.
            (ens r3=None;
             matches_prefix_sr r2 ns; a.
               (fun r4 -> reset (k r4)) a
             \/ (ex a. ens r3=Some a; r3)))
  <: matches_prefix_cps r1 ns k; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # rewrite "reset_under_bind"
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (matches_prefix_sr r1 ns; r3.
          reset
            ((fun r4 ->
               (fun r6 -> reset (k r6)) r4; r5.
                 (ens r5=None;
                  matches_prefix_sr r2 ns; a.
                    (fun r6 -> reset (k r6)) a
                  \/ (ex a. ens r5=Some a; r5))) r3))
  <: matches_prefix_cps r1 ns k; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # rewrite "IH"
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  subregex r1 r
  (2 more goals)
  
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall k : term, ns : term, r : term, r1 : term, r2 : term.
        (r = (TRDisj r1 r2)) -> (subregex r1 r)
  end
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ns
  module M
    use Heifer
    constant r1 : term
    constant r2 : term
    goal goal1 : subregex r1 (TRDisj r1 r2)
  end
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall r3.
    reset
      ((fun r4 ->
         reset
           ((fun r5 ->
              (fun r7 -> reset (k r7)) r5; r6.
                (ens r6=None;
                 matches_prefix_sr r2 ns; a.
                   (fun r7 -> reset (k r7)) a
                 \/ (ex a. ens r6=Some a; r6))) r4)) r3) <:
      (fun r4 ->
        reset
          ((fun r5 ->
             (fun r7 -> reset (k r7)) r5; r6.
               (ens r6=None;
                matches_prefix_sr r2 ns; a.
                  (fun r7 -> reset (k r7)) a
                \/ (ex a. ens r6=Some a; r6))) r4)) r3
  (1 more goals)
  
  
  # forall_intro ()
  
  k, ns, r, r0, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       ((fun r3 ->
          reset
            ((fun r4 ->
               (fun r6 -> reset (k r6)) r4; r5.
                 (ens r5=None;
                  matches_prefix_sr r2 ns; a.
                    (fun r6 -> reset (k r6)) a
                  \/ (ex a. ens r5=Some a; r5))) r3)) r0)
  <: (fun r3 ->
       reset
         ((fun r4 ->
            (fun r6 -> reset (k r6)) r4; r5.
              (ens r5=None;
               matches_prefix_sr r2 ns; a.
                 (fun r6 -> reset (k r6)) a
               \/ (ex a. ens r5=Some a; r5))) r3)) r0
  (1 more goals)
  
  
  # simpl ()
  
  k, ns, r, r0, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (reset
          (reset (k r0); r3.
             (ens r3=None;
              matches_prefix_sr r2 ns; a. reset (k a)
              \/ (ex a. ens r3=Some a; r3))))
  <: reset
       (reset (k r0); r3.
          (ens r3=None;
           matches_prefix_sr r2 ns; a. reset (k a)
           \/ (ex a. ens r3=Some a; r3)))
  (1 more goals)
  
  
  # rewrite "double_reset"
  
  k, ns, r, r0, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (reset (k r0); r3.
          (ens r3=None;
           matches_prefix_sr r2 ns; a. reset (k a)
           \/ (ex a. ens r3=Some a; r3)))
  <: reset
       (reset (k r0); r3.
          (ens r3=None;
           matches_prefix_sr r2 ns; a. reset (k a)
           \/ (ex a. ens r3=Some a; r3)))
  (1 more goals)
  
  
  # refl ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     matches_prefix_cps r1 ns
       (fun r3 ->
         reset
           ((fun r4 ->
              (fun r6 -> reset (k r6)) r4; r5.
                (ens r5=None;
                 matches_prefix_sr r2 ns; a.
                   (fun r6 -> reset (k r6)) a
                 \/ (ex a. ens r5=Some a; r5))) r3))
  <: matches_prefix_cps r1 ns k; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # axiom ~name:"matches_prefix_cps_cont"
      {| forall r ns k f.
      matches_prefix_cps r ns (fun r1 -> k r1; r2. f r2) <:
        matches_prefix_cps r ns k; r1. f r1
    |}
  axiom matches_prefix_cps_cont declared
  
  # rewrite ~direction:`Rtl "matches_prefix_cps_cont"
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     matches_prefix_cps r1 ns
       (fun r3 ->
         reset
           ((fun r4 ->
              (fun r6 -> reset (k r6)) r4; r5.
                (ens r5=None;
                 matches_prefix_sr r2 ns; a.
                   (fun r6 -> reset (k r6)) a
                 \/ (ex a. ens r5=Some a; r5))) r3))
  <: matches_prefix_cps r1 ns
       (fun r3 ->
         k r3; r4.
           (fun r5 ->
             ens r5=None; matches_prefix_cps r2 ns k \/ r5)
             r4)
  
  
  # congruence ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     (fun r3 ->
       reset
         ((fun r4 ->
            (fun r6 -> reset (k r6)) r4; r5.
              (ens r5=None;
               matches_prefix_sr r2 ns; a.
                 (fun r6 -> reset (k r6)) a
               \/ (ex a. ens r5=Some a; r5))) r3))
  <: (fun r3 ->
       k r3; r4.
         (fun r5 ->
           ens r5=None; matches_prefix_cps r2 ns k \/ r5) r4)
  
  
  # funext ()
  
  k, ns, r, r1, r2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall x.
    (fun r3 ->
      reset
        ((fun r4 ->
           (fun r6 -> reset (k r6)) r4; r5.
             (ens r5=None;
              matches_prefix_sr r2 ns; a.
                (fun r6 -> reset (k r6)) a
              \/ (ex a. ens r5=Some a; r5))) r3)) x <:
      (fun r3 ->
        k r3; r4.
          (fun r5 ->
            ens r5=None; matches_prefix_cps r2 ns k \/ r5) r4)
        x
  
  
  # forall_intro ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     (fun r3 ->
       reset
         ((fun r4 ->
            (fun r6 -> reset (k r6)) r4; r5.
              (ens r5=None;
               matches_prefix_sr r2 ns; a.
                 (fun r6 -> reset (k r6)) a
               \/ (ex a. ens r5=Some a; r5))) r3)) x0
  <: (fun r3 ->
       k r3; r4.
         (fun r5 ->
           ens r5=None; matches_prefix_cps r2 ns k \/ r5) r4)
       x0
  
  
  # simpl ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset
       (reset (k x0); r3.
          (ens r3=None;
           matches_prefix_sr r2 ns; a. reset (k a)
           \/ (ex a. ens r3=Some a; r3)))
  <: k x0; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # shift_reset_reduce ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (k x0); r3.
       (ens r3=None;
        reset (matches_prefix_sr r2 ns; a. reset (k a))
        \/ (ex a. ens r3=Some a; r3))
  <: k x0; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # rewrite "Hksf"
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     k x0; r3.
       (ens r3=None;
        reset (matches_prefix_sr r2 ns; a. reset (k a))
        \/ (ex a. ens r3=Some a; r3))
  <: k x0; r3.
       (ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # congruence ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     (fun r3 ->
       ens r3=None;
       reset (matches_prefix_sr r2 ns; a. reset (k a))
       \/ (ex a. ens r3=Some a; r3))
  <: (fun r3 ->
       ens r3=None; matches_prefix_cps r2 ns k \/ r3)
  
  
  # funext ()
  
  k, ns, r, r1, r2, x0
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall x1.
    (fun r3 ->
      ens r3=None;
      reset (matches_prefix_sr r2 ns; a. reset (k a))
      \/ (ex a. ens r3=Some a; r3)) x1 <:
      (fun r3 ->
        ens r3=None; matches_prefix_cps r2 ns k \/ r3) x1
  
  
  # forall_intro ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     (fun r3 ->
       ens r3=None;
       reset (matches_prefix_sr r2 ns; a. reset (k a))
       \/ (ex a. ens r3=Some a; r3)) x2
  <: (fun r3 ->
       ens r3=None; matches_prefix_cps r2 ns k \/ r3) x2
  
  
  # simpl ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x2=None;
     reset (matches_prefix_sr r2 ns; a. reset (k a))
     \/ (ex a. ens x2=Some a; x2)
  <: ens x2=None; matches_prefix_cps r2 ns k \/ x2
  
  
  # goal_is
      {|
     ens x2=None; reset (matches_prefix_sr r2 ns; a. reset (k a))
     \/ (ex a. ens x2=Some a; x2)
  <: ens x2=None; matches_prefix_cps r2 ns k \/ x2
  |}
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x2=None;
     reset (matches_prefix_sr r2 ns; a. reset (k a))
     \/ (ex a. ens x2=Some a; x2)
  <: ens x2=None; matches_prefix_cps r2 ns k \/ x2
  
  
  # disj_elim ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x2=None;
     reset (matches_prefix_sr r2 ns; a. reset (k a))
  <: ens x2=None; matches_prefix_cps r2 ns k \/ x2
  (1 more goals)
  
  
  # left ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x2=None;
     reset (matches_prefix_sr r2 ns; a. reset (k a))
  <: ens x2=None; matches_prefix_cps r2 ns k
  (1 more goals)
  
  
  # rewrite "IH"
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  subregex r2 r
  (3 more goals)
  
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall k : term, ns : term, r : term, r1 : term, r2 : term, x0 : term, x2 : term.
        (r = (TRDisj r1 r2)) -> (subregex r2 r)
  end
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ns
  Warning, file line 0, characters 0-0: unused variable x0
  Warning, file line 0, characters 0-0: unused variable x2
  module M
    use Heifer
    constant r1 : term
    constant r2 : term
    goal goal1 : subregex r2 (TRDisj r1 r2)
  end
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall r.
    reset ((fun r1 -> reset (k r1)) r) <:
      (fun r1 -> reset (k r1)) r
  (2 more goals)
  
  
  # simpl ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
  forall r. reset (reset (k r)) <: reset (k r)
  (2 more goals)
  
  
  # forall_intro ()
  
  k, ns, r, r0, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (reset (k r0))
  <: reset (k r0)
  (2 more goals)
  
  
  # rewrite "double_reset"
  
  k, ns, r, r0, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     reset (k r0)
  <: reset (k r0)
  (2 more goals)
  
  
  # refl ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x2=None;
     matches_prefix_cps r2 ns (fun r3 -> reset (k r3))
  <: ens x2=None; matches_prefix_cps r2 ns k
  (1 more goals)
  
  
  # rewrite "Hksf"
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x2=None; matches_prefix_cps r2 ns (fun r3 -> k r3)
  <: ens x2=None; matches_prefix_cps r2 ns k
  (1 more goals)
  
  
  # rewrite "eta_reduce"
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ens x2=None; matches_prefix_cps r2 ns k
  <: ens x2=None; matches_prefix_cps r2 ns k
  (1 more goals)
  
  
  # refl ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex a. ens x2=Some a; x2
  <: ens x2=None; matches_prefix_cps r2 ns k \/ x2
  
  
  # right ()
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex a. ens x2=Some a; x2
  <: x2
  
  
  # goal_is {|
     (ex a. ens x2=Some a; x2)
  <: x2
  |}
  
  k, ns, r, r1, r2, x0, x2
  Hksf: forall r. reset (k r) <: k r
  Hr: r=TRDisj r1 r2
  IH: forall r1.
        subregex r1 r =>
          (forall ns.
             (forall k.
                (forall r2. reset (k r2) <: k r2) =>
                  reset (matches_prefix_sr r1 ns; r2. k r2) <:
                    matches_prefix_cps r1 ns k))
  ────────────────────────────────────────────────────────────
     ex a. ens x2=Some a; x2
  <: x2
  
  
  # simple ()
  no more goals
  
  # qed ()
