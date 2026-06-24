  $ ./counter.exe
  
  # Options.fail_fast := true
  
  # declare
      {|
      countdown_loop get set =
        get (); v.
        ens v>0;
        set (v-1);
        countdown_loop get set
    |}
  countdown_loop declared
  
  # declare {| countdown get set n = set n; countdown_loop get set |}
  countdown declared
  
  # declare {| get1 _ = shift k (fun s -> k s; f. f s) |}
  get1 declared
  
  # declare {| set1 s = shift k (fun _ -> k (); f. f s) |}
  set1 declared
  
  # declare
      {|
      run_countdown1 n =
        reset (countdown get1 set1 n; fun _ -> ()); f.
        f 0
      |}
  run_countdown1 declared
  
  # declare {| get2 r = fun _ -> exists s. ens r->s; req r->s; s |}
  get2 declared
  
  # declare {| set2 r = fun s -> exists _. ens r->_; req r->s |}
  set2 declared
  
  # declare
      {|
      run_countdown2 n =
        forall r. req r->0;
        get2 r; get.
        set2 r; set.
        countdown get set n
    |}
  run_countdown2 declared
  
  # start_proof
      {| forall n. is_int n => run_countdown1 n <: run_countdown2 n |}
  
  ────────────────────────────────────────────────────────────
  forall n. is_int n => run_countdown1 n <: run_countdown2 n
  
  
  # forall_intro ()
  
  n
  ────────────────────────────────────────────────────────────
  is_int n => run_countdown1 n <: run_countdown2 n
  
  
  # intro_pure "Hn"
  
  n
  Hn: is_int n
  ────────────────────────────────────────────────────────────
     run_countdown1 n
  <: run_countdown2 n
  
  
  # unfold "run_countdown1"
  
  n
  Hn: is_int n
  ────────────────────────────────────────────────────────────
     reset (countdown get1 set1 n; (fun _ -> ())); f. f 0
  <: run_countdown2 n
  
  
  # unfold "run_countdown2"
  
  n
  Hn: is_int n
  ────────────────────────────────────────────────────────────
     reset (countdown get1 set1 n; (fun _ -> ())); f. f 0
  <: forall r.
       req r->0;
       get2 r; get. set2 r; set. countdown get set n
  
  
  # unfold "countdown"
  
  n
  Hn: is_int n
  ────────────────────────────────────────────────────────────
     reset
       ((set1 n; countdown_loop get1 set1); (fun _ -> ()));
       f. f 0
  <: forall r.
       req r->0;
       get2 r; get.
         set2 r; set. set n; countdown_loop get set
  
  
  # forall_intro ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
     reset
       ((set1 n; countdown_loop get1 set1); (fun _ -> ()));
       f. f 0
  <: req r->0;
     get2 r; get. set2 r; set. set n; countdown_loop get set
  
  
  # intro_heap ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset
       ((set1 n; countdown_loop get1 set1); (fun _ -> ()));
       f. f 0
  <: get2 r; get. set2 r; set. set n; countdown_loop get set
  
  
  # unfold "set1"
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset
       ((shift k (fun _ -> k (); f1. f1 n);
         countdown_loop get1 set1); (fun _ -> ())); f. 
       f 0
  <: get2 r; get. set2 r; set. set n; countdown_loop get set
  
  
  # shift_reset_reduce ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     (fun _ ->
       (fun _1 ->
         reset (countdown_loop get1 set1; (fun _2 -> ()))) ();
         f1. f1 n); f. f 0
  <: get2 r; get. set2 r; set. set n; countdown_loop get set
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     (fun _ ->
       reset (countdown_loop get1 set1; (fun _1 -> ())); f.
         f n) 0
  <: get2 r; get. set2 r; set. set n; countdown_loop get set
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: get2 r; get. set2 r; set. set n; countdown_loop get set
  
  
  # unfold "get2"
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: (fun _ -> ex s. ens r->s; req r->s; s); get.
       set2 r; set. set n; countdown_loop get set
  
  
  # unfold "set2"
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: (fun _ -> ex s. ens r->s; req r->s; s); get.
       (fun s -> ex _. ens r->_; req r->s); set.
         set n; countdown_loop get set
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: (fun s -> ex _. ens r->_; req r->s) n;
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: ex _.
       ens r->_;
       req r->n;
       countdown_loop (fun _1 -> ex s. ens r->s; req r->s; s)
         (fun s -> ex _1. ens r->_1; req r->s)
  
  
  # exists_intro ["0"]
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
  r->0
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: ens r->0;
     req r->n;
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # elim_heap ()
  
  n, r
  Hn: is_int n
  ────────────────────────────────────────────────────────────
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: req r->n;
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # induction ~name:"IH" (`Int 0) "n"
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: req r->n;
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # intro_heap ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f. f n
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # unfold "countdown_loop"
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       ((get1 (); v.
           ens v>0; set1 (v-1); countdown_loop get1 set1);
        (fun _ -> ())); f. f n
  <: (fun _ -> ex s. ens r->s; req r->s; s) (); v.
       ens v>0;
       (fun s -> ex _. ens r->_; req r->s) (v-1);
       countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
         (fun s -> ex _. ens r->_; req r->s)
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (get1 (); v.
          ens v>0;
          set1 (v-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ex s.
       ens r->s;
       req r->s;
       ens s>0;
       (ex _.
          ens r->_;
          req r->s-1;
          countdown_loop
            (fun _1 -> ex s1. ens r->s1; req r->s1; s1)
            (fun s1 -> ex _1. ens r->_1; req r->s1))
  
  
  # exists_intro ["n"]
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (get1 (); v.
          ens v>0;
          set1 (v-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ens r->n;
     req r->n;
     ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # elim_heap ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
     reset
       (get1 (); v.
          ens v>0;
          set1 (v-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: req r->n;
     ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # intro_heap ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (get1 (); v.
          ens v>0;
          set1 (v-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # unfold "get1"
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (shift k (fun s -> k s; f1. f1 s); v.
          ens v>0;
          set1 (v-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # shift_reset_reduce ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     (fun s ->
       (fun v ->
         reset
           (ens v>0;
            set1 (v-1);
            countdown_loop get1 set1; (fun _ -> ()))) s; f1.
         f1 s); f. f n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     (fun s ->
       reset
         (ens s>0;
          set1 (s-1); countdown_loop get1 set1; (fun _ -> ()));
         f. f s) n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (ens n>0;
        set1 (n-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # shift_reset_reduce ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     (ens n>0;
      reset
        (set1 (n-1); countdown_loop get1 set1; (fun _ -> ())));
       f. f n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # simpl ()
  
  n, r
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     ens n>0;
     reset
       (set1 (n-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # intro_pure "Hgt"
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (set1 (n-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ens n>0;
     (ex _.
        ens r->_;
        req r->n-1;
        countdown_loop
          (fun _1 -> ex s. ens r->s; req r->s; s)
          (fun s -> ex _1. ens r->_1; req r->s))
  
  
  # elim_pure ()
  Warning, file line 0, characters 0-0: unused variable r
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (set1 (n-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ex _.
       ens r->_;
       req r->n-1;
       countdown_loop (fun _1 -> ex s. ens r->s; req r->s; s)
         (fun s -> ex _1. ens r->_1; req r->s)
  
  
  # exists_intro ["n"]
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n
  ───────────────────────────────────────────────────────────*
     reset
       (set1 (n-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: ens r->n;
     req r->n-1;
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # elim_heap ()
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
     reset
       (set1 (n-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: req r->n-1;
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # intro_heap ()
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
     reset
       (set1 (n-1); countdown_loop get1 set1; (fun _ -> ()));
       f. f n
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # unfold "set1"
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
     reset
       (shift k (fun _ -> k (); f1. f1 (n-1));
        countdown_loop get1 set1; (fun _ -> ())); f. 
       f n
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # shift_reset_reduce ()
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
     (fun _ ->
       (fun _1 ->
         reset (countdown_loop get1 set1; (fun _2 -> ()))) ();
         f1. f1 (n-1)); f. f n
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # simpl ()
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
     (fun _ ->
       reset (countdown_loop get1 set1; (fun _1 -> ())); f.
         f (n-1)) n
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # simpl ()
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
     reset (countdown_loop get1 set1; (fun _ -> ())); f.
       f (n-1)
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # rewrite "IH"
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
  n-1>=0 /\ n-1<n
  (2 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable r
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
  is_int (n-1)
  (1 more goals)
  
  
  # pure_solver ()
  Warning, file line 0, characters 0-0: unused variable r
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
  r->n-1
  ───────────────────────────────────────────────────────────*
     req r->n-1;
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # elim_heap ()
  
  n, r
  Hgt: n>0
  Hn: is_int n
  IH: forall n1.
        n1>=0 /\ n1<n =>
          is_int n1 =>
            reset (countdown_loop get1 set1; (fun _ -> ()));
              f. f n1 <:
              req r->n1;
              countdown_loop
                (fun _ -> ex s. ens r->s; req r->s; s)
                (fun s -> ex _. ens r->_; req r->s)
  ────────────────────────────────────────────────────────────
     countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  <: countdown_loop (fun _ -> ex s. ens r->s; req r->s; s)
       (fun s -> ex _. ens r->_; req r->s)
  
  
  # refl ()
  no more goals
  
  # qed ()
  
  # Options.fail_fast := false
