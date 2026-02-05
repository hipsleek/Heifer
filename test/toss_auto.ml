open Heifer.Interactive;;

axiom ~name:"conj_false_l"
  {| forall t. (false /\ t) = false |}
;;

axiom ~name:"conj_false_r"
  {| forall t. (t /\ false) = false |}
;;

axiom ~name:"conj_true_l"
  {| forall t. (true /\ t) = t |}
;;

axiom ~name:"conj_true_r"
  {| forall t. (t /\ true) = t |}
;;

axiom ~name:"conj_assoc"
  {| forall t1 t2 t3. (t1 /\ (t2 /\ t3)) = ((t1 /\ t2) /\ t3) |}
;;

declare
  {| incr x = forall v. req x->v; ens x->v+1 |}
;;

declare
  {| do_toss x = shift k (incr x; k true; r1. incr x; k false; r2. r1 + r2) |}
;;

declare
  {| toss x = reset (do_toss x; r. (ens r=true; 1 \/ ens r=false; 0)) |}
;;

declare
  {|
    do_toss_n n x =
      ens n = 0; true \/
      ens n > 0; do_toss x; r1. do_toss_n (n-1) x; r2. r1 /\ r2
  |}
;;

declare
  {| toss_n n x = reset (do_toss_n n x; r. (ens r=true; 1 \/ ens r=false; 0)) |}
;;


lemma ~name:"do_toss_n_spec"
  {|
    forall n x a.
      reset (do_toss_n n x; r. (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      forall v. req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; (ens a=true; 1 \/ ens a=false; 0)
  |}
;;
forall_intro ();;
revert "a";;
goal_is
  {|
    forall a.
      reset (do_toss_n n x; r. (ens (a /\ r)=true; 1 \/ ens (a /\ r)=false; 0)) <:
      (forall v. req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; (ens a=true; 1 \/ ens a=false; 0))
  |}
;;
induction ~name:"IH" (`Int 0) "n";;
forall_intro ();;
unfold "do_toss_n";;
unfold "do_toss";;
unfold "incr";;
shift_reset_reduce ();;
simpl ();;
shift_reset_reduce ();;
simple ();;
qed ();;
