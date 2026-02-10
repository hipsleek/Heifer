open Heifer.Interactive;;

Options.fail_fast := true;;

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


lemma ~name:"toss_spec"
  {| forall x. toss x <: forall v. req is_int v; req x->v; ens x->v+2; 1 |}
;;
forall_intro ();;
forall_intro ();;
intro_pure "Hv";;
intro_heap ();;
unfold "toss";;
unfold "do_toss";;
unfold "incr";;
shift_reset_reduce ();;
simpl ();;
shift_reset_reduce ();;
let c = simple2 ();;
Format.printf "%a@." Prover.Automation.pp_cert (Option.get c);;
qed ();;


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
(* simple ();; *)
let c = simple2 ();;
Format.printf "%a@." Prover.Automation.pp_cert (Option.get c);;
qed ();;


lemma ~name:"toss_n_spec"
  {| forall n x. toss_n n x <: forall v. req is_int v; req x->v; ens x->v+pow 2 (n+1)-2; 1 |}
;;
forall_intro ();;
unfold "toss_n";;
have ~name:"H_eq_true" {| forall r. ens r=true <: ens (true /\ r)=true |};;
simple ();;
have ~name:"H_eq_false" {| forall r. ens r=false <: ens (true /\ r)=false |};;
simple ();;
rewrite "H_eq_true";;
rewrite "H_eq_false";;
clear_pure "H_eq_true";;
clear_pure "H_eq_false";;
rewrite "do_toss_n_spec";;
let c = simple2 ();;
Format.printf "%a@." Prover.Automation.pp_cert (Option.get c);;
qed ();;

Options.fail_fast := false;;
(* Statistics.report ();; *)
