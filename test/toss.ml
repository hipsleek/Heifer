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
      forall v. req x->v; ens x->v+pow 2 (n+1)-2; (ens a=true; 1 \/ ens a=false; 0)
  |}
;;

forall_intro ();;
revert "a";;
induction ~name:"IH" (`Int 0) "n";;
forall_intro ();;
unfold "do_toss_n";;
unfold "do_toss";;
unfold "incr";;
shift_reset_reduce ();;
simpl ();;
shift_reset_reduce ();;
disj_elim ();;

intro_pure "Hn";;
forall_intro ();;
intro_heap ();;
rewrite "Hn";;
have ~name:"H_eq" "v+pow 2 (0+1)-2 = v";;
admit ();;
rewrite "H_eq";;
clear_pure "H_eq";;
elim_heap ();;
rewrite "conj_true_r";;
refl ();;

rewrite ~direction:Direction.rtl "conj_assoc";;
rewrite "conj_true_r";;
rewrite "conj_false_r";;
rewrite "IH";;
pure_solver ();;
rewrite "IH";;
pure_solver ();;
clear_pure "IH";;
simpl ();;
intro_pure "Hn";;
forall_intro ();;
intro_heap ();;
forall_elim ["v"];;
elim_heap ();;
intro_heap ();;

forall_elim ["v+1"];;
elim_heap ();;
intro_heap ();;
disj_elim ();;

intro_pure "Ha";;
forall_elim ["v+1+pow 2 (n-1+1)-2"];;
elim_heap ();;
intro_heap ();;
forall_elim ["v+1+pow 2 (n-1+1)-2+1"];;
elim_heap ();;
have ~name:"H_eq" "v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2 = v+pow 2 (n+1)-2";;
admit ();;
rewrite "H_eq";;
clear_pure "H_eq";;
intro_heap ();;
elim_heap ();;
disj_elim ();;

intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;

intro_pure "_";;
left ();;
elim_pure ();;
prove ();;

intro_pure "Ha";;
forall_elim ["v+1+pow 2 (n-1+1)-2"];;
elim_heap ();;
intro_heap ();;
forall_elim ["v+1+pow 2 (n-1+1)-2+1"];;
elim_heap ();;
have ~name:"H_eq" "v+1+pow 2 (n-1+1)-2+1+pow 2 (n-1+1)-2 = v+pow 2 (n+1)-2";;
admit ();;
rewrite "H_eq";;
clear_pure "H_eq";;
intro_heap ();;
elim_heap ();;
disj_elim ();;

intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;

intro_pure "_";;
right ();;
elim_pure ();;
prove ();;
qed ();;


lemma ~name:"toss_spec"
  {| forall x. toss x <: forall v. req x->v; ens x->v+2; 1 |}
;;

forall_intro ();;
forall_intro ();;
intro_heap ();;
unfold "toss";;
unfold "do_toss";;
unfold "incr";;
shift_reset_reduce ();;
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


lemma ~name:"toss_n_spec"
  {| forall n x. toss_n n x <: forall v. req x->v; ens x->v+pow 2 (n+1)-2; 1 |}
;;

forall_intro ();;
forall_intro ();;
intro_heap ();;
unfold "toss_n";;
have ~name:"H_eq_true" {| forall r. ens r=true <: ens (true /\ r)=true |};;

forall_intro ();;
rewrite "conj_true_l";;
refl ();;

have ~name:"H_eq_false" {| forall r. ens r=false <: ens (true /\ r)=false |};;

forall_intro ();;
rewrite "conj_true_l";;
refl ();;

rewrite "H_eq_true";;
rewrite "H_eq_false";;
rewrite "do_toss_n_spec";;
clear_pure "H_eq_true";;
clear_pure "H_eq_false";;
forall_elim ["v"];;
elim_heap ();;
intro_heap ();;
elim_heap ();;
disj_elim ();;

intro_pure "_";;
refl ();;

intro_pure "H_absurd";;
ex_falso ();;
pure_solver ();;
qed ();;

Options.fail_fast := false;;
