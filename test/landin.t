
  $ ./landin.exe
  
  # Options.fail_fast := true
  
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
  
  # start_proof
      {|
      forall n. landin_rec factf; f. f n <: exists l f. ens l->f; fact n
    |}
  
  ────────────────────────────────────────────────────────────
  forall n.
    landin_rec factf; f. f n <: (ex l f. ens l->f; fact n)
  
  
  # forall_intro ()
  
  n
  ────────────────────────────────────────────────────────────
     landin_rec factf; f. f n
  <: ex l f. ens l->f; fact n
  
  
  # unfold "landin_rec"
  
  n
  ────────────────────────────────────────────────────────────
     (ex l g.
        ens l->();
        ens g=(fun n1 ->
                forall h. req l->h; ens l->h; factf h n1);
        (forall v. req l->v; ens l->g; g)); f. f n
  <: ex l f. ens l->f; fact n
  
  
  # goal_is
      {|
      (exists l g.
        ens l->();
        ens g=(fun n1 -> forall h. req l->h; ens l->h; factf h n1);
        (forall v. req l->v; ens l->g; g)); f. f n
      <: exists l f. ens l->f; fact n
    |}
  
  n
  ────────────────────────────────────────────────────────────
     (ex l g.
        ens l->();
        ens g=(fun n1 ->
                forall h. req l->h; ens l->h; factf h n1);
        (forall v. req l->v; ens l->g; g)); f. f n
  <: ex l f. ens l->f; fact n
  
  
  # exists_elim ()
  
  g, l, n
  ────────────────────────────────────────────────────────────
     (ens l->();
      ens g=(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
      (forall v. req l->v; ens l->g; g)); f. f n
  <: ex l f. ens l->f; fact n
  
  
  # simpl ()
  
  g, l, n
  ────────────────────────────────────────────────────────────
     ens l->();
     ens g=(fun n1 ->
             forall h. req l->h; ens l->h; factf h n1);
     (forall v. req l->v; ens l->g; g n)
  <: ex l f. ens l->f; fact n
  
  
  # ens_heap_elim ()
  
  g, l, n
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     ens g=(fun n1 ->
             forall h. req l->h; ens l->h; factf h n1);
     (forall v. req l->v; ens l->g; g n)
  <: ex l f. ens l->f; fact n
  
  
  # intro_pure "Hg"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     forall v. req l->v; ens l->g; g n
  <: ex l f. ens l->f; fact n
  
  
  # forall_elim ["()"]
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     req l->(); ens l->g; g n
  <: ex l f. ens l->f; fact n
  
  
  # simpl ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->()
  ───────────────────────────────────────────────────────────*
     req l->(); ens l->g; g n
  <: ex l f. ens l->f; fact n
  
  
  # req_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     ens l->g; g n
  <: ex l f. ens l->f; fact n
  
  
  # ens_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     g n
  <: ex l f. ens l->f; fact n
  
  
  # rewrite "Hg"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     (fun n1 -> forall h. req l->h; ens l->h; factf h n1) n
  <: ex l f. ens l->f; fact n
  
  
  # simpl ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     forall h. req l->h; ens l->h; factf h n
  <: ex l f. ens l->f; fact n
  
  
  # forall_elim ["g"]
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     req l->g; ens l->g; factf g n
  <: ex l f. ens l->f; fact n
  
  
  # req_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     ens l->g; factf g n
  <: ex l f. ens l->f; fact n
  
  
  # exists_intro ["l"; "g"]
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  ────────────────────────────────────────────────────────────
     ens l->g; factf g n
  <: ens l->g; fact n
  
  
  # induction ~name:"IH" (`Int 0) "n"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->g; factf g n
  <: ens l->g; fact n
  
  
  # unfold "factf"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->g; (ens n=0; 1 \/ ens n>0; g (n-1); r. n*.r)
  <: ens l->g; fact n
  
  
  # intro_heap ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     ens n=0; 1 \/ ens n>0; g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # disj_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     ens n=0; 1
  <: ens l->g; fact n
  (1 more goals)
  
  
  # goal_is {| ens n=0; 1 <: ens l->g; fact n |}
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     ens n=0; 1
  <: ens l->g; fact n
  (1 more goals)
  
  
  # intro_pure "Hn"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     1
  <: ens l->g; fact n
  (1 more goals)
  
  
  # ens_heap_intro ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n=0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     1
  <: fact n
  (1 more goals)
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable g
  Warning, file line 0, characters 0-0: unused variable l
  ==> Valid
  
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     ens n>0; g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # goal_is {| ens n>0; g (n-1); r. n*.r <: ens l->g; fact n |}
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     ens n>0; g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # intro_pure "Hn"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # revert_heap ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->g; g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # rewrite "Hg"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
     (fun n1 -> forall h. req l->h; ens l->h; factf h n1)
       (n-1); r. n*.r
  <: ens l->(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
     fact n
  
  
  # simpl ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
     (forall h. req l->h; ens l->h; factf h (n-1); r. n*.r)
  <: ens l->(fun n1 ->
              forall h. req l->h; ens l->h; factf h n1);
     fact n
  
  
  # rewrite ~direction:Direction.rtl "Hg"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->g;
     (forall h. req l->h; ens l->h; factf h (n-1); r. n*.r)
  <: ens l->g; fact n
  
  
  # ens_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     forall h. req l->h; ens l->h; factf h (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # forall_elim ["g"]
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     req l->g; ens l->g; factf g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # simpl ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     req l->g; ens l->g; factf g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # req_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->g; factf g (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # rewrite "IH"
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  n-1>=0 /\ n-1<n
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable l
  Warning, file line 0, characters 0-0: unused variable g
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     (ens l->g; fact (n-1)); r. n*.r
  <: ens l->g; fact n
  
  
  # simpl ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     ens l->g; fact (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # ens_heap_elim ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
  l->g
  ───────────────────────────────────────────────────────────*
     fact (n-1); r. n*.r
  <: ens l->g; fact n
  
  
  # ens_heap_intro ()
  
  g, l, n
  Hg: g=(fun n -> forall h. req l->h; ens l->h; factf h n)
  Hn: n>0
  IH: forall n1.
        n1>=0 /\ n1<n =>
          ens l->g; factf g n1 <: ens l->g; fact n1
  ────────────────────────────────────────────────────────────
     fact (n-1); r. n*.r
  <: fact n
  
  
  # prove ()
  Warning, file line 0, characters 0-0: unused variable g
  Warning, file line 0, characters 0-0: unused variable l
  ==> Valid
  
  no more goals
  
  # qed ()
  
  # Options.fail_fast := false
