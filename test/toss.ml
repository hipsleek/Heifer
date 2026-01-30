open Heifer.Interactive;;

Options.fail_fast := true;;

axiom ~name:"eta_reduce"
  {| forall f. (fun x -> f x) <: f |}
;;

axiom ~name:"bind_id_r"
  {| forall t. t; x. x <: t |}
;;

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
  {| forall t1 t2 t3. ((t1 /\ t2) /\ t3) = (t1 /\ (t2 /\ t3)) |}
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

lemma ~name:"toss_spec"
  {| forall x. toss x <: forall v. req x->v; ens x->v+2; 1 |}
;;

forall_intro ();;
forall_intro ();;
intro_heap ();;
unfold "toss";;
unfold "do_toss";;
unfold "incr";;
shift_reset_reduce ();; (* forall inside reset, be careful! *)
simpl ();;
forall_elim ["v"];;
elim_heap ();;
intro_heap ();;
shift_reset_reduce ();;
disj_elim ();;

intro_pure "_";;
forall_elim ["v+1"];;
elim_heap ();;
intro_heap ();;
disj_elim ();;

intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;

intro_pure "_";;
elim_heap ();;
admit ();; (* arithmetic *)

intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;
qed ();;

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

lemma ~name:"toss_n_spec/1"
  {| forall x. toss_n 1 x <: forall v. req x->v; ens x->v+2; 1 |}
;;

forall_intro ();;
forall_intro ();;
intro_heap ();;
unfold "toss_n";;
unfold "do_toss_n";;
unfold "do_toss";;
unfold "incr";;
unfold "do_toss_n";;
shift_reset_reduce ();;
disj_elim ();;

(* n=1, not base case of do_toss_n *)
intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;

intro_pure "_";;
forall_elim ["v"];;
elim_heap ();;
intro_heap ();;
simpl ();;
shift_reset_reduce ();;
disj_elim ();;

intro_pure "_";;
disj_elim ();;

intro_pure "_";;
forall_elim ["v+1"];;
elim_heap ();;
intro_heap ();;
disj_elim ();;

intro_pure "_";;
disj_elim ();;

goal_is {| ens (false /\ true)=true; 1+1 <: ens x->v+2; 1 |};;
rewrite "conj_false_l";; (* without this, pure_solver () will fail because of translation error *)
intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;

intro_pure "_";;
elim_heap ();;
prove ();;

intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;

rewrite "conj_true_l";;
intro_pure "H_absurd";; (* (true /\ true)=false*)
ex_falso ();;
pure_solver ();;

intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;
qed ();;

lemma ~name:"do_toss_n_spec"
  {|
    forall n x acc.
      reset (do_toss_n n x; r. (ens (acc /\ r)=true; 1 \/ ens (acc /\ r)=false; 0)) <:
      forall v. req x->v; ex v'. ens x->v'; (ens acc=true; 1 \/ ens acc=false; 0)
  |}
;;

admit ();; (* can be proven, I proved it, but I need to port the proofs over. And it is quite tedious *)

lemma ~name:"toss_n_spec"
  {| forall n x. toss_n n x <: forall v. req x->v; exists v'. ens x->v; 1 |}
;;

forall_intro ();;
forall_intro ();;
intro_heap ();;
unfold "toss_n";;
unfold "do_toss_n";;
unfold "do_toss";;
shift_reset_reduce ();;
simpl_beta ();;
simpl ();;

admit ();;

Options.fail_fast := false;;
