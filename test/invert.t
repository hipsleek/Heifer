  $ ./invert.exe
  
  # Options.fail_fast := true
  
  # declare
      {|
      iter f xs =
        ens xs=[]; () \/
        ex x xs'. ens xs=x::xs'; f x; iter f xs'
    |}
  iter declared
  
  # declare {| yield x = shift k (x::k) |}
  yield declared
  
  # declare {| invert xs = reset (iter yield xs; []) |}
  invert declared
  
  # declare
      {|
      to_seq xs =
        ens xs=[]; [] \/
        ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs')
    |}
  to_seq declared
  
  # start_proof {| forall xs. invert xs <: to_seq xs |}
  
  ────────────────────────────────────────────────────────────
  forall xs. invert xs <: to_seq xs
  
  
  # forall_intro ()
  
  xs
  ────────────────────────────────────────────────────────────
     invert xs
  <: to_seq xs
  
  
  # unfold "invert"
  
  xs
  ────────────────────────────────────────────────────────────
     reset (iter yield xs; [])
  <: to_seq xs
  
  
  # induction ~name:"IH" `List "xs"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     reset (iter yield xs; [])
  <: to_seq xs
  
  
  # unfold "iter"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     reset
       ((ens xs=[]; ()
         \/ (ex x xs'. ens xs=x::xs'; yield x; iter yield xs'));
        [])
  <: to_seq xs
  
  
  # unfold "to_seq"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     reset
       ((ens xs=[]; ()
         \/ (ex x xs'. ens xs=x::xs'; yield x; iter yield xs'));
        [])
  <: ens xs=[]; []
     \/ (ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs'))
  
  
  # shift_reset_reduce ()
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; []
     \/ (ex x xs'.
           ens xs=x::xs'; reset (yield x; iter yield xs'; []))
  <: ens xs=[]; []
     \/ (ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs'))
  
  
  # disj_elim ()
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; []
  <: ens xs=[]; []
     \/ (ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs'))
  (1 more goals)
  
  
  # left ()
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; []
  <: ens xs=[]; []
  (1 more goals)
  
  
  # refl ()
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs'; reset (yield x; iter yield xs'; [])
  <: ens xs=[]; []
     \/ (ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs'))
  
  
  # right ()
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs'; reset (yield x; iter yield xs'; [])
  <: ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs')
  
  
  # exists_elim ()
  
  x, xs, xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     ens xs=x::xs'; reset (yield x; iter yield xs'; [])
  <: ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs')
  
  
  # exists_intro ["x"; "xs'"]
  
  x, xs, xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     ens xs=x::xs'; reset (yield x; iter yield xs'; [])
  <: ens xs=x::xs'; x::(fun _ -> to_seq xs')
  
  
  # intro_pure "Hxs"
  
  x, xs, xs'
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     reset (yield x; iter yield xs'; [])
  <: ens xs=x::xs'; x::(fun _ -> to_seq xs')
  
  
  # elim_pure ()
  
  x, xs, xs'
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     reset (yield x; iter yield xs'; [])
  <: x::(fun _ -> to_seq xs')
  
  
  # unfold "yield"
  
  x, xs, xs'
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     reset (shift k (x::k); iter yield xs'; [])
  <: x::(fun _ -> to_seq xs')
  
  
  # shift_reset_reduce ()
  
  x, xs, xs'
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     x::(fun _ -> reset (iter yield xs'; []))
  <: x::(fun _ -> to_seq xs')
  
  
  # rewrite "IH"
  
  x, xs, xs'
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
  sublist xs' xs
  (1 more goals)
  
  
  # pure_solver ()
  
  x, xs, xs'
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          reset (iter yield xs1; []) <: to_seq xs1
  ────────────────────────────────────────────────────────────
     x::(fun _ -> to_seq xs')
  <: x::(fun _ -> to_seq xs')
  
  
  # refl ()
  no more goals
  
  # qed ()
  
  # Options.fail_fast := false

