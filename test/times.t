
  $ ./times.exe
  
  # Options.fail_fast := true
  
  # axiom ~name:"mult_0_l" {| forall x. 0*.x = 0 |}
  axiom mult_0_l declared
  
  # axiom ~name:"mult_0_r" {| forall x. x*.0 = 0 |}
  axiom mult_0_r declared
  
  # axiom ~name:"bind_id_r" {| forall t. t; x. x <: t |}
  axiom bind_id_r declared
  
  # declare
      {|
      times_sh xs =
        ens xs=[]; 1 \/
        ex x xs'. ens xs=x::xs'; (ens x=0; shift k 0 \/ times_sh xs'; r. x*.r)
    |}
  times_sh declared
  
  # axiom ~name:"times_sh_id_r"
      {| forall xs. times_sh xs <: times_sh xs; x. x |}
  axiom times_sh_id_r declared
  
  # declare {| times xs = reset (times_sh xs) |}
  times declared
  
  # declare
      {|
      times_cp xs k =
        ens xs=[]; k 1 \/
        ex x xs'. ens xs=x::xs'; (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
    |}
  times_cp declared
  
  # declare
      {|
      times_pure xs =
        ens xs=[]; 1 \/
        ex x xs'. ens xs=x::xs'; times_pure xs'; r. x*.r
    |}
  times_pure declared
  
  # axiom ~name:"times_pure_const_r"
      {| forall xs t. t <: times_pure xs; r. t |}
  axiom times_pure_const_r declared
  
  # lemma ~name:"times_sh/times_cp"
      {|
      forall xs k.
        (forall r. reset (k r) <: k r) =>
        reset (times_sh xs; r. k r) <: times_cp xs k
    |}
  
  ────────────────────────────────────────────────────────────
  forall xs k.
    (forall r. reset (k r) <: k r) =>
      reset (times_sh xs; r. k r) <: times_cp xs k
  
  
  # forall_intro ()
  
  k, xs
  ────────────────────────────────────────────────────────────
  (forall r. reset (k r) <: k r) =>
    reset (times_sh xs; r. k r) <: times_cp xs k
  
  
  # revert "k"
  
  xs
  ────────────────────────────────────────────────────────────
  forall k.
    (forall r. reset (k r) <: k r) =>
      reset (times_sh xs; r. k r) <: times_cp xs k
  
  
  # induction ~name:"IH" `List "xs"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
  forall k.
    (forall r. reset (k r) <: k r) =>
      reset (times_sh xs; r. k r) <: times_cp xs k
  
  
  # forall_intro ()
  
  k, xs
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
  (forall r. reset (k r) <: k r) =>
    reset (times_sh xs; r. k r) <: times_cp xs k
  
  
  # intro_pure "Hk"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset (times_sh xs; r. k r)
  <: times_cp xs k
  
  
  # unfold "times_sh"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset
       ((ens xs=[]; 1
         \/ (ex x xs'.
               ens xs=x::xs';
               (ens x=0; shift k1 0
                \/ times_sh xs'; r1. x*.r1))); r. k r)
  <: times_cp xs k
  
  
  # unfold "times_cp"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset
       ((ens xs=[]; 1
         \/ (ex x xs'.
               ens xs=x::xs';
               (ens x=0; shift k1 0
                \/ times_sh xs'; r1. x*.r1))); r. k r)
  <: ens xs=[]; k 1
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))))
  
  
  # shift_reset_reduce ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=[]; reset (k 1)
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0
            \/ reset (times_sh xs'; r. x*.r; r1. k r1)))
  <: ens xs=[]; k 1
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))))
  
  
  # disj_elim ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=[]; reset (k 1)
  <: ens xs=[]; k 1
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))))
  (1 more goals)
  
  
  # left ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=[]; reset (k 1)
  <: ens xs=[]; k 1
  (1 more goals)
  
  
  # rewrite "Hk"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k 1
  <: ens xs=[]; k 1
  (1 more goals)
  
  
  # refl ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       (ens x=0; 0 \/ reset (times_sh xs'; r. x*.r; r1. k r1))
  <: ens xs=[]; k 1
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))))
  
  
  # right ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       (ens x=0; 0 \/ reset (times_sh xs'; r. x*.r; r1. k r1))
  <: ex x xs'.
       ens xs=x::xs';
       (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  
  
  # exists_elim (); exists_intro ["x"; "xs'"]
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=x::xs';
     (ens x=0; 0 \/ reset (times_sh xs'; r. x*.r; r1. k r1))
  <: ex x xs'.
       ens xs=x::xs';
       (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=x::xs';
     (ens x=0; 0 \/ reset (times_sh xs'; r. x*.r; r1. k r1))
  <: ens xs=x::xs';
     (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  
  
  # intro_pure "Hxs"
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens x=0; 0 \/ reset (times_sh xs'; r. x*.r; r1. k r1)
  <: ens xs=x::xs';
     (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  
  
  # elim_pure ()
  Warning, file line 0, characters 0-0: unused variable k
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens x=0; 0 \/ reset (times_sh xs'; r. x*.r; r1. k r1)
  <: ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))
  
  
  # disj_elim ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens x=0; 0
  <: ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))
  (1 more goals)
  
  
  # left ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     ens x=0; 0
  <: ens x=0; 0
  (1 more goals)
  
  
  # refl ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset (times_sh xs'; r. x*.r; r1. k r1)
  <: ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))
  
  
  # right ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset (times_sh xs'; r. x*.r; r1. k r1)
  <: times_cp xs' (fun r -> k (x*.r))
  
  
  # simpl ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset (times_sh xs'; r. k (x*.r))
  <: times_cp xs' (fun r -> k (x*.r))
  
  
  # rewrite "IH"
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
  sublist xs' xs
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable k
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
  forall r.
    reset ((fun r1 -> k (x*.r1)) r) <:
      (fun r1 -> k (x*.r1)) r
  (1 more goals)
  
  
  # forall_intro ()
  
  k, r, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset ((fun r1 -> k (x*.r1)) r)
  <: (fun r1 -> k (x*.r1)) r
  (1 more goals)
  
  
  # simpl ()
  
  k, r, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     reset (k (x*.r))
  <: k (x*.r)
  (1 more goals)
  
  
  # rewrite "Hk"
  
  k, r, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     k (x*.r)
  <: k (x*.r)
  (1 more goals)
  
  
  # refl ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (times_sh xs1; r. k r) <: times_cp xs1 k)
  ────────────────────────────────────────────────────────────
     times_cp xs' (fun r -> k (x*.r))
  <: times_cp xs' (fun r -> k (x*.r))
  
  
  # refl ()
  no more goals
  
  # qed ()
  lemma times_sh/times_cp declared
  
  # lemma ~name:"times_cp/times_pure"
      {|
      forall xs k.
        (0 <: k 0) =>
        times_cp xs k <: times_pure xs; r. k r
    |}
  
  ────────────────────────────────────────────────────────────
  forall xs k.
    (0 <: k 0) => times_cp xs k <: times_pure xs; r. k r
  
  
  # forall_intro ()
  
  k, xs
  ────────────────────────────────────────────────────────────
  (0 <: k 0) => times_cp xs k <: times_pure xs; r. k r
  
  
  # revert "k"
  
  xs
  ────────────────────────────────────────────────────────────
  forall k.
    (0 <: k 0) => times_cp xs k <: times_pure xs; r. k r
  
  
  # induction ~name:"IH" `List "xs"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
  forall k.
    (0 <: k 0) => times_cp xs k <: times_pure xs; r. k r
  
  
  # forall_intro ()
  
  k, xs
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
  (0 <: k 0) => times_cp xs k <: times_pure xs; r. k r
  
  
  # intro_pure "Hk"
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     times_cp xs k
  <: times_pure xs; r. k r
  
  
  # unfold "times_cp"
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k 1
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))))
  <: times_pure xs; r. k r
  
  
  # unfold "times_pure"
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k 1
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))))
  <: (ens xs=[]; 1
      \/ (ex x xs'. ens xs=x::xs'; times_pure xs'; r1. x*.r1));
       r. k r
  
  
  # simpl ()
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k 1
     \/ (ex x xs'.
           ens xs=x::xs';
           (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))))
  <: ens xs=[]; k 1
     \/ (ex x xs'. ens xs=x::xs'; times_pure xs'; r. k (x*.r))
  
  
  # disj_elim ()
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k 1
  <: ens xs=[]; k 1
     \/ (ex x xs'. ens xs=x::xs'; times_pure xs'; r. k (x*.r))
  (1 more goals)
  
  
  # left ()
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k 1
  <: ens xs=[]; k 1
  (1 more goals)
  
  
  # refl ()
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  <: ens xs=[]; k 1
     \/ (ex x xs'. ens xs=x::xs'; times_pure xs'; r. k (x*.r))
  
  
  # right ()
  
  k, xs
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  <: ex x xs'. ens xs=x::xs'; times_pure xs'; r. k (x*.r)
  
  
  # exists_elim ()
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=x::xs';
     (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  <: ex x xs'. ens xs=x::xs'; times_pure xs'; r. k (x*.r)
  
  
  # exists_intro ["x"; "xs'"]
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=x::xs';
     (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  <: ens xs=x::xs'; times_pure xs'; r. k (x*.r)
  
  
  # intro_pure "Hxs"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))
  <: ens xs=x::xs'; times_pure xs'; r. k (x*.r)
  
  
  # elim_pure ()
  Warning, file line 0, characters 0-0: unused variable k
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r))
  <: times_pure xs'; r. k (x*.r)
  
  
  # disj_elim ()
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     ens x=0; 0
  <: times_pure xs'; r. k (x*.r)
  (1 more goals)
  
  
  # intro_pure "Hx"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hx: x=0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: times_pure xs'; r. k (x*.r)
  (1 more goals)
  
  
  # rewrite "Hx"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hx: x=0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: times_pure xs'; r. k (0*.r)
  (1 more goals)
  
  
  # rewrite "mult_0_l"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hx: x=0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: times_pure xs'; r. k 0
  (1 more goals)
  
  
  # rewrite ~direction:`Rtl "Hk"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hx: x=0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: times_pure xs'; r. 0
  (1 more goals)
  
  
  # goal_is "0 <: times_pure xs'; r. 0"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hx: x=0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: times_pure xs'; r. 0
  (1 more goals)
  
  
  # rewrite ~direction:`Rtl "times_pure_const_r"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hx: x=0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: 0
  (1 more goals)
  
  
  # refl ()
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     times_cp xs' (fun r -> k (x*.r))
  <: times_pure xs'; r. k (x*.r)
  
  
  # rewrite "IH"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
  sublist xs' xs
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable k
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: (fun r -> k (x*.r)) 0
  (1 more goals)
  
  
  # simpl ()
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: k (x*.0)
  (1 more goals)
  
  
  # rewrite "mult_0_r"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     0
  <: k 0
  (1 more goals)
  
  
  # rewrite "Hk"
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     k 0
  <: k 0
  (1 more goals)
  
  
  # refl ()
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     times_pure xs'; r. (fun r1 -> k (x*.r1)) r
  <: times_pure xs'; r. k (x*.r)
  
  
  # simpl ()
  
  k, x, xs, xs'
  Hk: 0 <: k 0
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (0 <: k 0) =>
               times_cp xs1 k <: times_pure xs1; r. k r)
  ────────────────────────────────────────────────────────────
     times_pure xs'; r. k (x*.r)
  <: times_pure xs'; r. k (x*.r)
  
  
  # refl ()
  no more goals
  
  # qed ()
  lemma times_cp/times_pure declared
  
  # start_proof {| forall xs. times xs <: times_pure xs |}
  
  ────────────────────────────────────────────────────────────
  forall xs. times xs <: times_pure xs
  
  
  # forall_intro ()
  
  xs
  ────────────────────────────────────────────────────────────
     times xs
  <: times_pure xs
  
  
  # unfold "times"
  
  xs
  ────────────────────────────────────────────────────────────
     reset (times_sh xs)
  <: times_pure xs
  
  
  # rewrite "times_sh_id_r"
  
  xs
  ────────────────────────────────────────────────────────────
     reset (times_sh xs; x. x)
  <: times_pure xs
  
  
  # rewrite "times_sh/times_cp"
  
  xs
  ────────────────────────────────────────────────────────────
  forall r. reset ((fun r1 -> r1) r) <: (fun r1 -> r1) r
  (1 more goals)
  
  
  # forall_intro ()
  
  r, xs
  ────────────────────────────────────────────────────────────
     reset ((fun r1 -> r1) r)
  <: (fun r1 -> r1) r
  (1 more goals)
  
  
  # simpl ()
  
  r, xs
  ────────────────────────────────────────────────────────────
     reset (r)
  <: r
  (1 more goals)
  
  
  # shift_reset_reduce ()
  
  r, xs
  ────────────────────────────────────────────────────────────
     r
  <: r
  (1 more goals)
  
  
  # refl ()
  
  xs
  ────────────────────────────────────────────────────────────
     times_cp xs (fun r -> r)
  <: times_pure xs
  
  
  # rewrite "times_cp/times_pure"
  
  xs
  ────────────────────────────────────────────────────────────
     0
  <: (fun r -> r) 0
  (1 more goals)
  
  
  # simpl ()
  
  xs
  ────────────────────────────────────────────────────────────
     0
  <: 0
  (1 more goals)
  
  
  # refl ()
  
  xs
  ────────────────────────────────────────────────────────────
     times_pure xs; r. (fun r1 -> r1) r
  <: times_pure xs
  
  
  # simpl ()
  
  xs
  ────────────────────────────────────────────────────────────
     times_pure xs; r. r
  <: times_pure xs
  
  
  # rewrite "bind_id_r"
  
  xs
  ────────────────────────────────────────────────────────────
     times_pure xs
  <: times_pure xs
  
  
  # refl ()
  no more goals
  
  # qed ()
  
  # Options.fail_fast := false
