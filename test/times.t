
  $ ./times.exe
  
  # declare
      {| times xs =
      ens xs=[]; 1
      \/ (ex ys. ens xs=0::ys; shift k 0)
      \/ ex x ys. ens xs=x::ys; times ys; r. x*.r
    |}
  times declared
  
  # start_proof
      {| forall xs x. is_int_list xs => is_int x =>
     reset (times xs; r. x*r)
  <: product (x::xs)
  |}
  
  ────────────────────────────────────────────────────────────
  forall xs x.
    is_int_list xs =>
      is_int x =>
        reset (times xs; r. x * r) <: product (x::xs)
  
  
  # forall_intro ()
  
  x, xs
  ────────────────────────────────────────────────────────────
  is_int_list xs =>
    is_int x => reset (times xs; r. x * r) <: product (x::xs)
  
  
  # intro_pure "Htxs"
  
  x, xs
  Htxs: is_int_list xs
  ────────────────────────────────────────────────────────────
  is_int x => reset (times xs; r. x * r) <: product (x::xs)
  
  
  # revert "x"
  
  xs
  Htxs: is_int_list xs
  ────────────────────────────────────────────────────────────
  forall x.
    is_int x => reset (times xs; r. x * r) <: product (x::xs)
  
  
  # induction ~name:"IH" `List "xs"
  
  xs
  Htxs: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            (forall x.
               is_int x =>
                 reset (times xs1; r. x * r) <:
                   product (x::xs1))
  ────────────────────────────────────────────────────────────
  forall x.
    is_int x => reset (times xs; r. x * r) <: product (x::xs)
  
  
  # start_proof
      {| forall xs. is_int_list xs =>
       reset (times xs)
    <: product xs
  |}
  
  ────────────────────────────────────────────────────────────
  forall xs. is_int_list xs => reset (times xs) <: product xs
  
  
  # forall_intro ()
  
  xs
  ────────────────────────────────────────────────────────────
  is_int_list xs => reset (times xs) <: product xs
  
  
  # intro_pure "Hty"
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     reset (times xs)
  <: product xs
  
  
  # unfold "times"
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     reset
       (ens xs=[]; 1 \/ (ex ys. ens xs=0::ys; shift k 0)
        \/ (ex x ys. ens xs=x::ys; times ys; r. x*.r))
  <: product xs
  
  
  # shift_reset_reduce ()
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ens xs=[]; 1 \/ (ex ys. ens xs=0::ys; 0)
     \/ (ex x ys. ens xs=x::ys; reset (times ys; r. x*.r))
  <: product xs
  
  
  # disj_elim ()
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ens xs=[]; 1 \/ (ex ys. ens xs=0::ys; 0)
  <: product xs
  (1 more goals)
  
  
  # disj_elim ()
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ens xs=[]; 1
  <: product xs
  (2 more goals)
  
  
  # goal_is {|
     ens xs=[]; 1
  <: product xs
  |}
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ens xs=[]; 1
  <: product xs
  (2 more goals)
  
  
  # intro_pure "Hxs"
  
  xs
  Hty: is_int_list xs
  Hxs: xs=[]
  ────────────────────────────────────────────────────────────
     1
  <: product xs
  (2 more goals)
  
  
  # prove ()
  ==> Valid
  
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ex ys. ens xs=0::ys; 0
  <: product xs
  (1 more goals)
  
  
  # goal_is {|
     (ex ys. ens xs=0::ys; 0)
  <: product xs
  |}
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ex ys. ens xs=0::ys; 0
  <: product xs
  (1 more goals)
  
  
  # exists_elim ()
  
  xs, ys
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ens xs=0::ys; 0
  <: product xs
  (1 more goals)
  
  
  # intro_pure "Hxs"
  
  xs, ys
  Hty: is_int_list xs
  Hxs: xs=0::ys
  ────────────────────────────────────────────────────────────
     0
  <: product xs
  (1 more goals)
  
  
  # prove ()
  ==> Valid
  
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ex x ys. ens xs=x::ys; reset (times ys; r. x*.r)
  <: product xs
  
  
  # goal_is
      {|
     (ex x ys. ens xs=x::ys; reset (times ys; r. x*.r))
  <: product xs
  |}
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ex x ys. ens xs=x::ys; reset (times ys; r. x*.r)
  <: product xs
  
  
  # exists_elim ()
  
  x, xs, ys
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     ens xs=x::ys; reset (times ys; r. x*.r)
  <: product xs
  
  
  # intro_pure "Hxs"
  
  x, xs, ys
  Hty: is_int_list xs
  Hxs: xs=x::ys
  ────────────────────────────────────────────────────────────
     reset (times ys; r. x*.r)
  <: product xs
  
