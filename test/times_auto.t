
  $ ./times_auto.exe
  
  # Options.fail_fast := true
  
  # Options.ignore_why3_failure := true
  
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
  
  
  # simple ()
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable r
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable r
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
  
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable k
  no more goals
  
  # Format.printf "%a@." Prover.Automation.pp_cert (Option.get c)
  disj_elim ();
  ( left ();
    refl (); )
  ( right ();
    exists_elim ();
    intro_pure "H";
    disj_elim ();
    ( exists_intro ["x"; "xs'"];
      intro_pure "H0";
      elim_pure ();
      rewrite "H0" (* x=0 *);
      rewrite "mult_0_l" (* forall x. 0*.x=0 *);
      rewrite "Hk" (* 0 <: k 0 *);
      prove () (* 0 <: times_pure xs'; r. 0 *) )
    ( exists_intro ["x"; "xs'"];
      elim_pure ();
      rewrite "IH" (* forall xs1.
                        sublist xs1 xs =>
                          (forall k.
                             (0 <: k 0) =>
                               times_cp xs1 k <:
                                 times_pure xs1; r. k r) *);
      ( prove () (* sublist xs' xs *) );
      ( rewrite "mult_0_r" (* forall x. x*.0=0 *);
        rewrite "Hk" (* 0 <: k 0 *);
        refl (); )
      refl (); ) )
  
  # qed ()
  lemma times_cp/times_pure declared
  
  # Options.fail_fast := false
  
  # Options.ignore_why3_failure := false
