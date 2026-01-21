
  $ ./append.exe
  
  # declare
      {| append_s xs =
      ens xs=[]; shift k k
      \/ ex x ys. ens xs=x::ys; append_s ys; r. x::r
    |}
  append_s declared
  
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
  
  # start_proof
      {| forall xs ys. is_list xs => is_list ys =>
       reset (append_s xs) ys
    <: append_pure xs ys
  |}
  
  ────────────────────────────────────────────────────────────
  forall xs ys.
    is_list xs =>
      is_list ys =>
        reset (append_s xs) ys <: append_pure xs ys
  
