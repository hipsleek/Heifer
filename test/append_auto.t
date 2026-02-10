
  $ ./append_auto.exe
  
  # Options.fail_fast := true
  
  # axiom ~name:"eta_reduce" {| forall f. (fun x -> f x) <: f |}
  axiom eta_reduce declared
  
  # axiom ~name:"bind_id_r" {| forall t. t; x. x <: t |}
  axiom bind_id_r declared
  
  # declare
      {|
      append_sh xs =
        ens xs=[]; shift k k \/
        exists x xs'. ens xs=x::xs'; append_sh xs'; r. x::r
    |}
  append_sh declared
  
  # axiom ~name:"append_sh_bind_id_r"
      {| forall xs. append_sh xs <: append_sh xs; x. x |}
  axiom append_sh_bind_id_r declared
  
  # declare {| append_delim xs ys = reset (append_sh xs); f. f ys |}
  append_delim declared
  
  # declare
      {|
      append_cps xs k =
        ens xs=[]; k \/
        exists x xs'. ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))
    |}
  append_cps declared
  
  # declare
      {|
      append_pure xs ys =
        ens xs=[]; ys \/
        exists x xs'. ens xs=x::xs'; append_pure xs' ys; r. x::r
    |}
  append_pure declared
  
  # lemma ~name:"append_sh/append_cps"
      {|
      forall xs k.
        (forall r. reset (k r) <: k r) =>
        reset (append_sh xs; r. k r) <: append_cps xs k
    |}
  
  ────────────────────────────────────────────────────────────
  forall xs k.
    (forall r. reset (k r) <: k r) =>
      reset (append_sh xs; r. k r) <: append_cps xs k
  
  
  # forall_intro ()
  
  k, xs
  ────────────────────────────────────────────────────────────
  (forall r. reset (k r) <: k r) =>
    reset (append_sh xs; r. k r) <: append_cps xs k
  
  
  # revert "k"
  
  xs
  ────────────────────────────────────────────────────────────
  forall k.
    (forall r. reset (k r) <: k r) =>
      reset (append_sh xs; r. k r) <: append_cps xs k
  
  
  # induction ~name:"IH" `List "xs"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
  forall k.
    (forall r. reset (k r) <: k r) =>
      reset (append_sh xs; r. k r) <: append_cps xs k
  
  
  # forall_intro ()
  
  k, xs
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
  (forall r. reset (k r) <: k r) =>
    reset (append_sh xs; r. k r) <: append_cps xs k
  
  
  # intro_pure "Hk"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset (append_sh xs; r. k r)
  <: append_cps xs k
  
  
  # unfold "append_sh"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset
       ((ens xs=[]; shift k1 k1
         \/ (ex x xs'.
               ens xs=x::xs'; append_sh xs'; r1. x::r1)); r.
          k r)
  <: append_cps xs k
  
  
  # unfold "append_cps"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset
       ((ens xs=[]; shift k1 k1
         \/ (ex x xs'.
               ens xs=x::xs'; append_sh xs'; r1. x::r1)); r.
          k r)
  <: ens xs=[]; k
     \/ (ex x xs'.
           ens xs=x::xs'; append_cps xs' (fun r -> k (x::r)))
  
  
  # shift_reset_reduce ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=[]; (fun r -> reset (k r))
     \/ (ex x xs'.
           ens xs=x::xs';
           reset (append_sh xs'; r. x::r; r1. k r1))
  <: ens xs=[]; k
     \/ (ex x xs'.
           ens xs=x::xs'; append_cps xs' (fun r -> k (x::r)))
  
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
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable r
  no more goals
  
  # qed ()
  lemma append_sh/append_cps declared
  
  # Format.printf "%a@." Prover.Automation.pp_cert (Option.get c)
  disj_elim ();
  ( left ();
    intro_pure "H";
    elim_pure ();
    rewrite "Hk" (* forall r. reset (k r) <: k r *);
    rewrite "eta_reduce" (* forall f. (fun x -> f x) <: f *);
    refl (); )
  ( right ();
    exists_elim ();
    intro_pure "H";
    exists_intro ["x"; "xs'"];
    elim_pure ();
    rewrite "IH" (* forall xs1.
                      sublist xs1 xs =>
                        (forall k.
                           (forall r. reset (k r) <: k r) =>
                             reset (append_sh xs1; r. k r) <:
                               append_cps xs1 k) *);
    ( prove () (* sublist xs' xs *) );
    ( forall_intro ();
      rewrite "Hk" (* forall r. reset (k r) <: k r *);
      refl (); )
    refl (); )
  
  # lemma ~name:"append_cps/append_pure"
      {|
      forall xs ys k.
        append_cps xs k; f. f ys <: append_pure xs ys; r. k r
    |}
  
  ────────────────────────────────────────────────────────────
  forall xs ys k.
    append_cps xs k; f. f ys <: append_pure xs ys; r. k r
  
  
  # forall_intro ()
  
  k, xs, ys
  ────────────────────────────────────────────────────────────
     append_cps xs k; f. f ys
  <: append_pure xs ys; r. k r
  
  
  # revert "k"
  
  xs, ys
  ────────────────────────────────────────────────────────────
  forall k.
    append_cps xs k; f. f ys <: append_pure xs ys; r. k r
  
  
  # induction ~name:"IH" `List "xs"
  
  xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
  forall k.
    append_cps xs k; f. f ys <: append_pure xs ys; r. k r
  
  
  # forall_intro ()
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     append_cps xs k; f. f ys
  <: append_pure xs ys; r. k r
  
  
  # unfold "append_cps"
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     (ens xs=[]; k
      \/ (ex x xs'.
            ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))));
       f. f ys
  <: append_pure xs ys; r. k r
  
  
  # unfold "append_pure"
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     (ens xs=[]; k
      \/ (ex x xs'.
            ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))));
       f. f ys
  <: (ens xs=[]; ys
      \/ (ex x xs'.
            ens xs=x::xs'; append_pure xs' ys; r1. x::r1));
       r. k r
  
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  Warning, file line 0, characters 0-0: unused variable ys
  no more goals
  
  # Format.printf "%a@." Prover.Automation.pp_cert (Option.get c)
  disj_elim ();
  ( left ();
    refl (); )
  ( right ();
    exists_elim ();
    intro_pure "H";
    exists_intro ["x"; "xs'"];
    elim_pure ();
    rewrite "IH" (* forall xs1.
                      sublist xs1 xs =>
                        (forall k.
                           append_cps xs1 k; f. f ys <:
                             append_pure xs1 ys; r. k r) *);
    ( prove () (* sublist xs' xs *) )
    refl (); )
  
  # qed ()
  lemma append_cps/append_pure declared
  
  # Options.fail_fast := false
