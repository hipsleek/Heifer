
  $ ./append.exe
  
  # declare
      {| append_sh xs =
      ens xs=[]; shift k k
      \/ ex x ys. ens xs=x::ys; append_sh ys; r. x::r
    |}
  append_sh declared
  
  # declare
      {| append_cps xs k =
      ens xs=[]; k []
      \/ ex x ys. ens xs=x::ys; append_cps ys (fun r -> k (x::r))
    |}
  append_cps declared
  
  # declare
      {| append_pure xs ys =
      ens xs=[]; ys
      \/ ex x ys. ens xs=x::ys; append_pure xs ys
    |}
  append_pure declared
  
  # declare {| append_delim xs ys =
      reset (append_sh xs); f. f ys
    |}
  append_delim declared
  
  # start_proof
      {| forall xs ys. is_list xs => is_list ys =>
       append_delim xs ys
    <: append_pure xs ys
  |}
  
  ────────────────────────────────────────────────────────────
  forall xs ys.
    is_list xs =>
      is_list ys => append_delim xs ys <: append_pure xs ys
  
  
  # unfold "append_delim"
  
  ────────────────────────────────────────────────────────────
  forall xs ys.
    is_list xs =>
      is_list ys =>
        reset (append_sh xs); f. f ys <: append_pure xs ys
  
  
  # forall_intro ()
  
  xs, ys
  ────────────────────────────────────────────────────────────
  is_list xs =>
    is_list ys =>
      reset (append_sh xs); f. f ys <: append_pure xs ys
  
  
  # intro_pure "Htx"
  
  xs, ys
  Htx: is_list xs
  ────────────────────────────────────────────────────────────
  is_list ys =>
    reset (append_sh xs); f. f ys <: append_pure xs ys
  
  
  # intro_pure "Hty"
  
  xs, ys
  Htx: is_list xs
  Hty: is_list ys
  ────────────────────────────────────────────────────────────
     reset (append_sh xs); f. f ys
  <: append_pure xs ys
  
  
  # unfold "append_sh"
  
  xs, ys
  Htx: is_list xs
  Hty: is_list ys
  ────────────────────────────────────────────────────────────
     reset
       (ens xs=[]; shift k k
        \/ (ex x ys1. ens xs=x::ys1; append_sh ys1; r. x::r));
       f. f ys
  <: append_pure xs ys
  
  
  # shift_reset_reduce ()
  
  xs, ys
  Htx: is_list xs
  Hty: is_list ys
  ────────────────────────────────────────────────────────────
     (ens xs=[]; (fun x -> x)
      \/ (ex x ys1.
            ens xs=x::ys1; reset (append_sh ys1; r. x::r)));
       f. f ys
  <: append_pure xs ys
  
  
  # simpl ()
  
  xs, ys
  Htx: is_list xs
  Hty: is_list ys
  ────────────────────────────────────────────────────────────
     ens xs=[]; ys
     \/ (ex x ys1.
           ens xs=x::ys1; reset (append_sh ys1; r. x::r)); f.
          f ys
  <: append_pure xs ys
  
  
  # disj_elim ()
  
  xs, ys
  Htx: is_list xs
  Hty: is_list ys
  ────────────────────────────────────────────────────────────
     ens xs=[]; ys
  <: append_pure xs ys
  (1 more goals)
  
  
  # admit ()
  
  xs, ys
  Htx: is_list xs
  Hty: is_list ys
  ────────────────────────────────────────────────────────────
     (ex x ys1. ens xs=x::ys1; reset (append_sh ys1; r. x::r));
       f. f ys
  <: append_pure xs ys
  
