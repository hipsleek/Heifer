  $ ./landin_auto.exe
  
  # Options.fail_fast := true
  
  # Options.ignore_why3_failure := true
  
  # declare
      {|
      landin_rec f =
        exists l g.
          ens l->();
          ens g=(fun n -> forall h. req l->h; ens l->h; f h n);
          forall v. req l->v; ens l->g;
          g
    |}
  landin_rec declared
  
  # declare
      {|
      factf self n =
        ens n=0; 1 \/
        ens n>0; self (n-1); r. n*.r
    |}
  factf declared
  
  # start_proof {|
      forall n. landin_rec factf; f. f n <: fact n
    |}
  
  ────────────────────────────────────────────────────────────
  forall n. landin_rec factf; f. f n <: fact n
  
  
  # forall_intro ()
  
  n
  ────────────────────────────────────────────────────────────
     landin_rec factf; f. f n
  <: fact n
  
  
  # unfold "landin_rec"
  
  n
  ────────────────────────────────────────────────────────────
     (ex l g.
        ens l->();
        ens g=(fun n1 ->
                forall h. req l->h; ens l->h; factf h n1);
        (forall v. req l->v; ens l->g; g)); f. f n
  <: fact n
  
  
  # simpl ()
  
  n
  ────────────────────────────────────────────────────────────
     ex l g.
       ens l->();
       ens g=(fun n1 ->
               forall h. req l->h; ens l->h; factf h n1);
       (forall v. req l->v; ens l->g; g n)
  <: fact n
  
  
  # exists_elim ()
  
  g, l, n
  ────────────────────────────────────────────────────────────
     ens l->();
     ens g=(fun n1 ->
             forall h. req l->h; ens l->h; factf h n1);
     (forall v. req l->v; ens l->g; g n)
  <: fact n
  
  
  # ens_heap_elim ()
  
  g, l, n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     ens g=(fun n1 ->
             forall h. req l->h; ens l->h; factf h n1);
     (forall v. req l->v; ens l->g; g n)
  <: fact n
  
  
  # intro_pure "Hg"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     forall v. req l->v; ens l->g; g n
  <: fact n
  
  
  # forall_elim ["()"]
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     req l->(); ens l->g; g n
  <: fact n
  
  
  # req_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     ens l->g; g n
  <: fact n
  
  
  # ens_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     g n
  <: fact n
  
  
  # rewrite "Hg"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     (fun n1 -> forall h. req l->h; ens l->h; factf h n1) n
  <: fact n
  
  
  # simpl ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     forall h. req l->h; ens l->h; factf h n
  <: fact n
  
  
  # forall_elim ["g"]
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     req l->g; ens l->g; factf g n
  <: fact n
  
  
  # req_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     ens l->g; factf g n
  <: fact n
  
  
  # ens_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     factf g n
  <: fact n
  
  
  # revert_heap ~side:`Rhs ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     factf g n
  <: req l->g; fact n
  
  
  # goal_is {| factf g n <: req l-> g; fact n |}
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     factf g n
  <: req l->g; fact n
  
  
  # rewrite "Hg"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     factf
       (fun n1 -> forall h. req l->h; ens l->h; factf h n1) n
  <: req l->(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
     fact n
  
  
  # induction ~name:"IH" (`Int 0) "n"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          factf
            (fun n2 ->
              forall h. req l->h; ens l->h; factf h n2) n1 <:
            req l->(fun n2 ->
                     forall h. req l->h; ens l->h; factf h n2);
            fact n1
  ────────────────────────────────────────────────────────────
     factf
       (fun n1 -> forall h. req l->h; ens l->h; factf h n1) n
  <: req l->(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
     fact n
  
  
  # unfold ~side:`Lhs "factf"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          factf
            (fun n2 ->
              forall h. req l->h; ens l->h; factf h n2) n1 <:
            req l->(fun n2 ->
                     forall h. req l->h; ens l->h; factf h n2);
            fact n1
  ────────────────────────────────────────────────────────────
     ens n=0; 1
     \/ ens n>0;
        (fun n1 -> forall h. req l->h; ens l->h; factf h n1)
          (n-1); r. n*.r
  <: req l->(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
     fact n
  
  Warning, file line 0, characters 0-0: unused variable g
  Warning, file line 0, characters 0-0: unused variable l
  Warning, file line 0, characters 0-0: unused variable g
  Warning, file line 0, characters 0-0: unused variable l
  Warning, file line 0, characters 0-0: unused variable g
  Warning, file line 0, characters 0-0: unused variable l
  Warning, file line 0, characters 0-0: unused variable g
  Warning, file line 0, characters 0-0: unused variable l
  no more goals
  
  # Format.printf "%a@." Prover.Automation.pp_cert (Option.get c)
  disj_elim ();
  ( intro_pure "H";
    intro_heap ();
    prove () (* 1 <: fact n *) )
  ( intro_pure "H";
    intro_heap ();
    forall_elim ["(fun n ->
                    forall h. req l->h; ens l->h; factf h n)"];
    elim_heap ();
    intro_heap ();
    rewrite "IH" (* forall n1.
                      n1>=0 /\ n1<n =>
                        factf
                          (fun n2 ->
                            forall h.
                              req l->h; ens l->h; factf h n2)
                          n1 <:
                          req l->(fun n2 ->
                                   forall h.
                                     req l->h;
                                     ens l->h; factf h n2);
                          fact n1 *);
    ( prove () (* n-1>=0 /\ n-1<n *) )
    elim_heap ();
    prove () (* fact (n-1); r. n*.r <: fact n *) )
  
  # qed ()
  
  # Options.fail_fast := false
  
  # Options.ignore_why3_failure := false
