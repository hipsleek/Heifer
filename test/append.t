
  $ ./append.exe
  
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
  lemma append_sh/append_cps declared
  
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
  
  
  # disj_elim ()
  
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
  <: ens xs=[]; k
     \/ (ex x xs'.
           ens xs=x::xs'; append_cps xs' (fun r -> k (x::r)))
  (1 more goals)
  
  
  # left ()
  
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
  <: ens xs=[]; k
  (1 more goals)
  
  
  # intro_pure "Hxs"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=[]
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     (fun r -> reset (k r))
  <: ens xs=[]; k
  (1 more goals)
  
  
  # ens_pure_intro ()
  Warning, file line 0, characters 0-0: unused variable k
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=[]
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     (fun r -> reset (k r))
  <: k
  (1 more goals)
  
  
  # rewrite "Hk"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=[]
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     (fun r -> k r)
  <: k
  (1 more goals)
  
  
  # rewrite "eta_reduce"
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=[]
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     k
  <: k
  (1 more goals)
  
  
  # refl ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       reset (append_sh xs'; r. x::r; r1. k r1)
  <: ens xs=[]; k
     \/ (ex x xs'.
           ens xs=x::xs'; append_cps xs' (fun r -> k (x::r)))
  
  
  # right ()
  
  k, xs
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       reset (append_sh xs'; r. x::r; r1. k r1)
  <: ex x xs'.
       ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))
  
  
  # exists_elim (); exists_intro ["x"; "xs'"]
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=x::xs'; reset (append_sh xs'; r. x::r; r1. k r1)
  <: ex x xs'.
       ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))
  
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     ens xs=x::xs'; reset (append_sh xs'; r. x::r; r1. k r1)
  <: ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))
  
  
  # intro_pure "Hxs"
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset (append_sh xs'; r. x::r; r1. k r1)
  <: ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))
  
  
  # elim_pure ()
  Warning, file line 0, characters 0-0: unused variable k
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset (append_sh xs'; r. x::r; r1. k r1)
  <: append_cps xs' (fun r -> k (x::r))
  
  
  # simpl ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset (append_sh xs'; r. k (x::r))
  <: append_cps xs' (fun r -> k (x::r))
  
  
  # rewrite "IH"
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
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
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
  forall r.
    reset ((fun r1 -> k (x::r1)) r) <:
      (fun r1 -> k (x::r1)) r
  (1 more goals)
  
  
  # forall_intro ()
  
  k, r, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset ((fun r1 -> k (x::r1)) r)
  <: (fun r1 -> k (x::r1)) r
  (1 more goals)
  
  
  # simpl ()
  
  k, r, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     reset (k (x::r))
  <: k (x::r)
  (1 more goals)
  
  
  # rewrite "Hk"
  
  k, r, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     k (x::r)
  <: k (x::r)
  (1 more goals)
  
  
  # refl ()
  
  k, x, xs, xs'
  Hk: forall r. reset (k r) <: k r
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             (forall r. reset (k r) <: k r) =>
               reset (append_sh xs1; r. k r) <:
                 append_cps xs1 k)
  ────────────────────────────────────────────────────────────
     append_cps xs' (fun r -> k (x::r))
  <: append_cps xs' (fun r -> k (x::r))
  
  
  # refl ()
  no more goals
  
  # qed ()
  no more goals
  
  # lemma ~name:"append_cps/append_pure"
      {|
      forall xs ys k.
        append_cps xs k; f. f ys <: append_pure xs ys; r. k r
    |}
  lemma append_cps/append_pure declared
  
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
  
  
  # simpl ()
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k ys
     \/ (ex x xs'.
           ens xs=x::xs'; append_cps xs' (fun r -> k (x::r)));
          f. f ys
  <: ens xs=[]; k ys
     \/ (ex x xs'.
           ens xs=x::xs'; append_pure xs' ys; r1. x::r1); r.
          k r
  
  
  # disj_elim ()
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k ys
  <: ens xs=[]; k ys
     \/ (ex x xs'.
           ens xs=x::xs'; append_pure xs' ys; r1. x::r1); r.
          k r
  (1 more goals)
  
  
  # left ()
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=[]; k ys
  <: ens xs=[]; k ys
  (1 more goals)
  
  
  # refl ()
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     (ex x xs'.
        ens xs=x::xs'; append_cps xs' (fun r -> k (x::r)));
       f. f ys
  <: ens xs=[]; k ys
     \/ (ex x xs'.
           ens xs=x::xs'; append_pure xs' ys; r1. x::r1); r.
          k r
  
  
  # right ()
  
  k, xs, ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     (ex x xs'.
        ens xs=x::xs'; append_cps xs' (fun r -> k (x::r)));
       f. f ys
  <: (ex x xs'. ens xs=x::xs'; append_pure xs' ys; r1. x::r1);
       r. k r
  
  
  # exists_elim ()
  
  k, x, xs, xs', ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     (ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))); f.
       f ys
  <: (ex x xs'. ens xs=x::xs'; append_pure xs' ys; r1. x::r1);
       r. k r
  
  
  # exists_intro ["x"; "xs'"]
  
  k, x, xs, xs', ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     (ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))); f.
       f ys
  <: (ens xs=x::xs'; append_pure xs' ys; r1. x::r1); r. k r
  
  
  # simpl ()
  
  k, x, xs, xs', ys
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     ens xs=x::xs';
     append_cps xs' (fun r -> k (x::r)); f. f ys
  <: ens xs=x::xs'; append_pure xs' ys; r. k (x::r)
  
  
  # intro_pure "Hxs"
  
  k, x, xs, xs', ys
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     append_cps xs' (fun r -> k (x::r)); f. f ys
  <: ens xs=x::xs'; append_pure xs' ys; r. k (x::r)
  
  
  # elim_pure ()
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  
  k, x, xs, xs', ys
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     append_cps xs' (fun r -> k (x::r)); f. f ys
  <: append_pure xs' ys; r. k (x::r)
  
  
  # rewrite "IH"
  
  k, x, xs, xs', ys
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
  sublist xs' xs
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable ys
  Warning, file line 0, characters 0-0: unused variable k
  
  k, x, xs, xs', ys
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     append_pure xs' ys; r. (fun r1 -> k (x::r1)) r
  <: append_pure xs' ys; r. k (x::r)
  
  
  # simpl ()
  
  k, x, xs, xs', ys
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          (forall k.
             append_cps xs1 k; f. f ys <:
               append_pure xs1 ys; r. k r)
  ────────────────────────────────────────────────────────────
     append_pure xs' ys; r. k (x::r)
  <: append_pure xs' ys; r. k (x::r)
  
  
  # refl ()
  no more goals
  
  # qed ()
  no more goals
  
  # start_proof {| forall xs ys. append_delim xs ys <: append_pure xs ys |}
  
  ────────────────────────────────────────────────────────────
  forall xs ys. append_delim xs ys <: append_pure xs ys
  
  
  # forall_intro ()
  
  xs, ys
  ────────────────────────────────────────────────────────────
     append_delim xs ys
  <: append_pure xs ys
  
  
  # unfold "append_delim"
  
  xs, ys
  ────────────────────────────────────────────────────────────
     reset (append_sh xs); f. f ys
  <: append_pure xs ys
  
  
  # rewrite "append_sh_bind_id_r"
  
  xs, ys
  ────────────────────────────────────────────────────────────
     reset (append_sh xs; x. x); f. f ys
  <: append_pure xs ys
  
  
  # rewrite "append_sh/append_cps"
  
  xs, ys
  ────────────────────────────────────────────────────────────
  forall r. reset ((fun r1 -> r1) r) <: (fun r1 -> r1) r
  (1 more goals)
  
  
  # forall_intro ()
  
  r, xs, ys
  ────────────────────────────────────────────────────────────
     reset ((fun r1 -> r1) r)
  <: (fun r1 -> r1) r
  (1 more goals)
  
  
  # simpl ()
  
  r, xs, ys
  ────────────────────────────────────────────────────────────
     reset (r)
  <: r
  (1 more goals)
  
  
  # shift_reset_reduce ()
  
  r, xs, ys
  ────────────────────────────────────────────────────────────
     r
  <: r
  (1 more goals)
  
  
  # refl ()
  
  xs, ys
  ────────────────────────────────────────────────────────────
     append_cps xs (fun r -> r); f. f ys
  <: append_pure xs ys
  
  
  # rewrite "append_cps/append_pure"
  
  xs, ys
  ────────────────────────────────────────────────────────────
     append_pure xs ys; r. (fun r1 -> r1) r
  <: append_pure xs ys
  
  
  # simpl ()
  
  xs, ys
  ────────────────────────────────────────────────────────────
     append_pure xs ys; r. r
  <: append_pure xs ys
  
  
  # rewrite "bind_id_r"
  
  xs, ys
  ────────────────────────────────────────────────────────────
     append_pure xs ys
  <: append_pure xs ys
  
  
  # refl ()
  no more goals
  
  # qed ()
  no more goals
  
  # Options.fail_fast := false
