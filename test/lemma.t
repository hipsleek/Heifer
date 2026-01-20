
  $ ./lemma.exe
  start_proof {|
    (ex x. ens x->1; read x) <: 1
  |}
  
  
  ────────────────────────────────────────────────────────────
     ex x. ens x->1; read x
  <: 1
  
  axiom ~name:"H" "forall x. read x <: forall v. req x->v; ens x->v; v"
  
  
  H: forall x. read x <: (forall v. req x->v; ens x->v; v)
  ────────────────────────────────────────────────────────────
     ex x. ens x->1; read x
  <: 1
  
  exists_elim ()
  
  x
  H: forall x. read x <: (forall v. req x->v; ens x->v; v)
  ────────────────────────────────────────────────────────────
     ens x->1; read x
  <: 1
  
  rewrite "H"
  
  x
  H: forall x. read x <: (forall v. req x->v; ens x->v; v)
  ────────────────────────────────────────────────────────────
     ens x->1; (forall v. req x->v; ens x->v; v)
  <: 1
  
  intro_heap ()
  
  x
  H: forall x. read x <: (forall v. req x->v; ens x->v; v)
  ────────────────────────────────────────────────────────────
  x->1
  ───────────────────────────────────────────────────────────*
     forall v. req x->v; ens x->v; v
  <: 1
  
  forall_elim ["1"]
  
  x
  H: forall x. read x <: (forall v. req x->v; ens x->v; v)
  ────────────────────────────────────────────────────────────
  x->1
  ───────────────────────────────────────────────────────────*
     req x->1; ens x->1; 1
  <: 1
  
  req_heap_elim ()
  
  x
  H: forall x. read x <: (forall v. req x->v; ens x->v; v)
  ────────────────────────────────────────────────────────────
     ens x->1; 1
  <: 1
  
  ens_heap_elim ()
  
  x
  H: forall x. read x <: (forall v. req x->v; ens x->v; v)
  ────────────────────────────────────────────────────────────
  x->1
  ───────────────────────────────────────────────────────────*
     1
  <: 1
  
  refl ()
  no more goals
  qed ()
  no more goals
