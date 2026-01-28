open Heifer.Interactive;;

axiom ~name:"eta_reduce"
  {| forall f. (fun x -> f x) <: f |}
;;

axiom ~name:"bind_id_r"
  {| forall t. t; x. x <: t |}
;;

declare
  {| incr x = forall v. req x->v; ens x->v+1 |}
;;

declare
  {| do_toss x = shift k (incr x; k true; r1. incr x; k false; r2. r1 + r2) |}
;;

declare
  {| toss x = reset (do_toss x; v. (ens v=true; 1 \/ ens v=false; 0)) |}
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
admit ();; (* discriminate/absurd *)

intro_pure "_0";;
elim_heap ();;
admit ();; (* arithmetic *)

intro_pure "H_absurd";;
admit ();; (* discriminate/absurd *)
qed ();;
