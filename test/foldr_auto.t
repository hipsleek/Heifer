
  $ ./foldr_auto.exe
  
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
  
  ==> Valid
  
  ==> Valid
  
  ==> Valid
  
  ==> Valid
  
  
  # qed ()
  
  # Format.printf "%a@." Prover.Tactic.Automation.pp_cert
      ((pf |> Result.get_ok) |> fst)
  disj_elim ();
  ( intro_pure "_";
    rewrite "_" (* xs=[] *);
    prove () (* 0 <: sum [] *) )
  ( exists_elim ();
    intro_pure "_";
    rewrite "_" (* xs=x::xs' *);
    rewrite "_" (* forall xs1.
                     sublist xs1 xs =>
                       is_int_list xs1 =>
                         foldr (fun x acc -> x+acc) 0 xs1 <:
                           sum xs1 *);
    ( rewrite "_" (* xs=x::xs' *);
      prove () (* sublist xs' (x::xs') *) );
    ( prove () (* is_int_list xs' *) )
    prove () (* sum xs'; r. x+r <: sum (x::xs') *) )

