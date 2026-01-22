open Heifer.Interactive;;

declare
  {| loop2 x y z = forall a.
  (req z->a /\ a>0; ens z->a; incr y x; decr z 1; loop2 x y z) /\
  (req z->a /\ a<=0; ens z->a)
  |}
;;

declare {| ds1 y z = ens y->0 * z->2*.x; loop2 x y z; read y |};;
declare {| ds2 y z = ens y->0 * z->x; loop2 x y z; read y; r. r*.2 |};;

start_proof
  {| forall x y z.
     loop2 x y z
  <: forall a b. req is_nat b; req y->a * z->b; ens y->(a+b*.x) * z->0
|}
;;

forall_intro ();;
forall_intro ();;
intro_pure "Htyb";;
revert "a";;
induction ~name:"IH" (`Int 0) "b";;
forall_intro ();;

goal_is {|
     loop2 x y z
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
|};;

unfold "loop2";;

goal_is
  {| forall a.
       (req z->a /\ a>0;
        ens z->a; incr y x; decr z 1; loop2 x y z) /\
         (req z->a /\ a<=0; ens z->a)
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
|}
;;

forall_elim ["b"];;

(* case b > 0 *)
case ~name:"Hb" "b > 0";;
conj_elim_l ();;

goal_is
  {|
     req z->b /\ b>0;
     ens z->b; incr y x; decr z 1; loop2 x y z
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
|}
;;

req_heap_intro ();;
axiom ~name:"Hh" {| forall p q. req p /\ q <: req p; req q |};;

(* Prover.Proof_context.Options.notation := false;; *)
(* Prover.Proof_context.Options.notation := true;; *)

rewrite "Hh";;
simpl ();;
req_heap_elim ();;
prove ();;
revert_heap ();;
axiom ~name:"H_ens_swap" {| forall p q. ens p; ens q <: ens q; ens p |};;
rewrite "H_ens_swap";;
simpl ();;

(* axiom ~name:"Hread" "forall x. ens x->v; read x <: ens x->v; v";; *)

axiom ~name:"Hincr" {| forall x y v. ens x->v; incr x y <: ens x->v+y |};;
rewrite "Hincr";;
rewrite "H_ens_swap";;
simpl ();;
axiom ~name:"Hdecr" {| forall x y v. ens x->v; decr x y <: ens x->v-y |};;
rewrite "Hdecr";;

goal_is {|
     ens y->a1+x; ens z->b-1; loop2 x y z
  <: ens y->a1+b*.x * z->0
|};;

intro_heap ();;
intro_heap ();;
specialize "IH" ["b-1"];;
forward "IH";;
prove ();;
forward "IH";;
prove ();;
specialize "IH" ["a1+x"];;
rewrite "IH";;

goal_is {|
     req y->a1+x * z->b-1; ens y->a1+x+(b-1)*.x * z->0
  <: ens y->a1+b*.x * z->0
|};;

req_heap_elim ();;
ens_heap_elim ();;
ens_heap_intro ();;
Options.show_why3_goal := true;;
prove ();;

(* case b <= 0 *)
conj_elim_r ();;

goal_is {|
     req z->b /\ b<=0; ens z->b
  <: req y->a1 * z->b; ens y->a1+b*.x * z->0
|};;

axiom ~name:"Hh" {| forall p q. req p /\ q <: req p; req q |};;
rewrite "Hh";;
simpl ();;
req_heap_intro ();;
req_heap_elim ();;
Options.show_why3_goal := true;;
prove ();;
ens_heap_elim ();;
ens_heap_intro ();;
prove ();;
qed ()
