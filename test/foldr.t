
  $ ./foldr.exe
  
  # Options.fail_fast := true
  
  # declare
      {|
      foldr f acc xs =
        ens xs=[]; acc \/
        ex x xs'. ens xs=x::xs'; foldr f acc xs'; r. f x r
    |}
  foldr declared
  
  # start_proof
      {| forall xs. is_int_list xs => foldr (fun x acc -> x + acc) 0 xs <: sum xs |}
  
  ────────────────────────────────────────────────────────────
  forall xs.
    is_int_list xs =>
      foldr (fun x acc -> x+acc) 0 xs <: sum xs
  
  
  # forall_intro ()
  
  xs
  ────────────────────────────────────────────────────────────
  is_int_list xs => foldr (fun x acc -> x+acc) 0 xs <: sum xs
  
  
  # intro_pure "Hty"
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     foldr (fun x acc -> x+acc) 0 xs
  <: sum xs
  
  
  # goal_is "foldr (fun x acc -> x+acc) 0 xs <: sum xs"
  
  xs
  Hty: is_int_list xs
  ────────────────────────────────────────────────────────────
     foldr (fun x acc -> x+acc) 0 xs
  <: sum xs
  
  
  # induction ~name:"IH" `List "xs"
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun x acc -> x+acc) 0 xs
  <: sum xs
  
  
  # unfold "foldr"
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
     \/ (ex x xs'.
           ens xs=x::xs';
           foldr (fun x1 acc -> x1+acc) 0 xs'; r.
             (fun x1 acc -> x1+acc) x r)
  <: sum xs
  
  
  # goal_is
      {|
      ens xs=[]; 0 \/
      (ex x xs'.
        ens xs=x::xs';
        foldr (fun x1 acc -> x1+acc) 0 xs'; r. (fun x1 acc -> x1+acc) x r)
      <: sum xs
    |}
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
     \/ (ex x xs'.
           ens xs=x::xs';
           foldr (fun x1 acc -> x1+acc) 0 xs'; r.
             (fun x1 acc -> x1+acc) x r)
  <: sum xs
  
  
  # disj_elim ()
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
  <: sum xs
  (1 more goals)
  
  
  # goal_is "ens xs=[]; 0 <: sum xs"
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=[]; 0
  <: sum xs
  (1 more goals)
  
  
  # intro_pure "Hxs"
  
  xs
  Hty: is_int_list xs
  Hxs: xs=[]
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     0
  <: sum xs
  (1 more goals)
  
  
  # prove ()
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       foldr (fun x1 acc -> x1+acc) 0 xs'; r.
         (fun x1 acc -> x1+acc) x r
  <: sum xs
  
  
  # goal_is
      {|
      (ex x xs'.
        ens xs=x::xs';
        foldr (fun x1 acc -> x1+acc) 0 xs'; r. (fun x1 acc -> x1+acc) x r)
      <: sum xs
    |}
  
  xs
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ex x xs'.
       ens xs=x::xs';
       foldr (fun x1 acc -> x1+acc) 0 xs'; r.
         (fun x1 acc -> x1+acc) x r
  <: sum xs
  
  
  # exists_elim ()
  
  x, xs, xs'
  Hty: is_int_list xs
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     ens xs=x::xs';
     foldr (fun x1 acc -> x1+acc) 0 xs'; r.
       (fun x1 acc -> x1+acc) x r
  <: sum xs
  
  
  # intro_pure "Hxs"
  
  x, xs, xs'
  Hty: is_int_list xs
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun x1 acc -> x1+acc) 0 xs'; r.
       (fun x1 acc -> x1+acc) x r
  <: sum xs
  
  
  # goal_is
      {|
      foldr (fun x1 acc -> x1+acc) 0 xs'; r. (fun x1 acc -> x1+acc) x r
      <: sum xs
    |}
  
  x, xs, xs'
  Hty: is_int_list xs
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     foldr (fun x1 acc -> x1+acc) 0 xs'; r.
       (fun x1 acc -> x1+acc) x r
  <: sum xs
  
  
  # rewrite "IH"
  
  x, xs, xs'
  Hty: is_int_list xs
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
  sublist xs' xs
  (2 more goals)
  
  
  # prove ()
  
  x, xs, xs'
  Hty: is_int_list xs
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
  is_int_list xs'
  (1 more goals)
  
  
  # prove ()
  
  x, xs, xs'
  Hty: is_int_list xs
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum xs'; r. (fun x1 acc -> x1+acc) x r
  <: sum xs
  
  
  # goal_is {|
      sum xs'; r. (fun x1 acc -> x1+acc) x r
      <: sum xs
    |}
  
  x, xs, xs'
  Hty: is_int_list xs
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum xs'; r. (fun x1 acc -> x1+acc) x r
  <: sum xs
  
  
  # simpl ()
  
  x, xs, xs'
  Hty: is_int_list xs
  Hxs: xs=x::xs'
  IH: forall xs1.
        sublist xs1 xs =>
          is_int_list xs1 =>
            foldr (fun x acc -> x+acc) 0 xs1 <: sum xs1
  ────────────────────────────────────────────────────────────
     sum xs'; r. x+r
  <: sum xs
  
  
  # Options.show_why3_goal := true
  
  # prove ()
  module M
    use heifer.Heifer
    
    goal goal1:
      forall x : term, xs : term, xs' : term.
        (xs = (TCons x xs'))
          ->
          (xs.is_int_list)
          ->
          ((plus x (xs'.sum)) = (xs.sum))
  end
  module M
    use Heifer
    constant x : term
    constant xs' : term
    axiom H : is_int_list (TCons x xs')
    goal goal1 : plus x (sum xs') = sum (TCons x xs')
  end
  no more goals
  
  # Options.show_why3_goal := false
  
  # qed ()
  
  # Options.fail_fast := false
