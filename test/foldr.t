
  $ ./foldr.exe
  declare
      {|foldr f init xs =
    ens xs=[]; init
    \/ ex h t. ens xs=h::t; foldr f init t; r. f h r|}
  foldr declared
  start_proof "forall xs. foldr (fun c t -> c + t) 0 xs <: sum xs"
  
  ────────────────────────────────────────────────────────────
  forall xs. foldr (fun c t -> c+t) 0 xs <: sum xs
  
  forall_intro ()
  
  xs
  ────────────────────────────────────────────────────────────
     foldr (fun c t -> c+t) 0 xs
  <: sum xs
  
  goal_is "foldr (fun c t -> c+t) 0 xs <: sum xs"
  
  xs
  ────────────────────────────────────────────────────────────
     foldr (fun c t -> c+t) 0 xs
  <: sum xs
  
  induction ~name:"IH" `List "xs"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun c t -> c+t) 0 xs
  <: sum xs
  
  unfold "foldr"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
     \/ (ex h t.
           ens xs=h::t;
           foldr (fun c t1 -> c+t1) 0 t; r.
             (fun c t1 -> c+t1) h r)
  <: sum xs
  
  goal_is
      {|
     ens xs=[]; 0
     \/ (ex h t.
           ens xs=h::t;
           foldr (fun c t1 -> c+t1) 0 t; r.
             (fun c t1 -> c+t1) h r)
  <: sum xs
  |}
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
     \/ (ex h t.
           ens xs=h::t;
           foldr (fun c t1 -> c+t1) 0 t; r.
             (fun c t1 -> c+t1) h r)
  <: sum xs
  
  disj_elim ()
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
  <: sum xs
  (1 more goals)
  
  goal_is "ens xs=[]; 0 <: sum xs"
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
  <: sum xs
  (1 more goals)
  
  intro_pure "H"
  
  xs
  H: xs=[]
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     0
  <: sum xs
  (1 more goals)
  
  prove ()
  ==> Valid
  
  
  xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ex h t.
       ens xs=h::t;
       foldr (fun c t1 -> c+t1) 0 t; r.
         (fun c t1 -> c+t1) h r
  <: sum xs
  
  goal_is
      {|
     ex h t.
       ens xs=h::t;
       foldr (fun c t1 -> c+t1) 0 t; r.
         (fun c t1 -> c+t1) h r
  <: sum xs
  |}
  error: goal was expected to be
    ex h t.
      ens xs=h::t; foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r <:
        sum xs
  but was:
    (ex h t.
       ens xs=h::t; foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r) <:
      sum xs
  exists_elim ()
  
  h, t, xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=h::t;
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  intro_pure "Hxs"
  
  h, t, xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  goal_is
      {|
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  |}
  
  h, t, xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  rewrite "IH"
  
  h, t, xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
  sublist t xs
  (1 more goals)
  
  prove ()
  ==> Valid
  
  
  h, t, xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  goal_is {|
     sum t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  |}
  
  h, t, xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  simpl ()
  
  h, t, xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum t; r. h+r
  <: sum xs
  
  prove ()
  ==> Valid
  
  no more goals
  qed ()
  no more goals
