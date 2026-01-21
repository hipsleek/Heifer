
  $ ./foldr.exe
  
  # declare
      {|foldr f init xs =
    ens xs=[]; init
    \/ ex h t. ens xs=h::t; foldr f init t; r. f h r|}
  foldr declared
  
  # start_proof
      "forall xs. is_int_list xs => foldr (fun c t -> c + t) 0 xs <: sum xs"
  
  ────────────────────────────────────────────────────────────
  forall xs.
    is_int_list xs => foldr (fun c t -> c+t) 0 xs <: sum xs
  
  
  # forall_intro ()
  
  xs
  ────────────────────────────────────────────────────────────
  is_int_list xs => foldr (fun c t -> c+t) 0 xs <: sum xs
  
  
  # intro_pure "Hty"
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     foldr (fun c t -> c+t) 0 xs
  <: sum xs
  
  
  # goal_is "foldr (fun c t -> c+t) 0 xs <: sum xs"
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     foldr (fun c t -> c+t) 0 xs
  <: sum xs
  
  
  # induction ~name:"IH" `List "xs"
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun c t -> c+t) 0 xs
  <: sum xs
  
  
  # unfold "foldr"
  
  xs
  Hty: is_int_list xs
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
  
  
  # goal_is
      {|
     ens xs=[]; 0
     \/ (ex h t.
           ens xs=h::t;
           foldr (fun c t1 -> c+t1) 0 t; r.
             (fun c t1 -> c+t1) h r)
  <: sum xs
  |}
  
  xs
  Hty: is_int_list xs
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
  
  
  # disj_elim ()
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
  <: sum xs
  (1 more goals)
  
  
  # goal_is "ens xs=[]; 0 <: sum xs"
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
  <: sum xs
  (1 more goals)
  
  
  # intro_pure "H"
  
  xs
  H: xs=[]
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     0
  <: sum xs
  (1 more goals)
  
  
  # prove ()
  ==> Valid
  
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ex h t.
       ens xs=h::t;
       foldr (fun c t1 -> c+t1) 0 t; r.
         (fun c t1 -> c+t1) h r
  <: sum xs
  
  
  # goal_is
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
  
  # exists_elim ()
  
  h, t, xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=h::t;
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  
  # intro_pure "Hxs"
  
  h, t, xs
  Hty: is_int_list xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  
  # goal_is
      {|
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  |}
  
  h, t, xs
  Hty: is_int_list xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  
  # rewrite "IH"
  
  h, t, xs
  Hty: is_int_list xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
  sublist t xs
  (1 more goals)
  
  
  # prove ()
  ==> Valid
  
  
  h, t, xs
  Hty: is_int_list xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  
  # goal_is {|
     sum t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  |}
  
  h, t, xs
  Hty: is_int_list xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum t; r. (fun c t1 -> c+t1) h r
  <: sum xs
  
  
  # simpl ()
  
  h, t, xs
  Hty: is_int_list xs
  Hxs: xs=h::t
  IH: forall xs1.
        sublist xs1 xs =>
          foldr (fun c t -> c+t) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum t; r. h+r
  <: sum xs
  
  
  # Options.show_why3_goal := true
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall h : term, t : term, xs : term.
        (xs.is_int_list)
          ->
          (xs = (TCons h t))
          ->
          ((plus h (t.sum)) = (xs.sum))
  end
  module M
    use Heifer
    constant h : term
    constant t : term
    axiom H : is_int_list (TCons h t)
    goal goal1 : plus h (sum t) = sum (TCons h t)
  end
  ==> Valid
  
  no more goals
  
  # qed ()
  no more goals
