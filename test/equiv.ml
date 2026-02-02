open Heifer.Interactive;;

Options.fail_fast := true;;

declare
  {|
    loop2 x y z =
      forall a.
        (req z->a /\ a>0; ens z->a; incr y x; decr z 1; loop2 x y z) /\
        (req z->a /\ a<=0; ens z->a)
  |}
;;

axiom ~name:"incr_spec"
  {| forall l x. incr l x <: forall v. req l->v; ens l->v+x |}
;;

axiom ~name:"decr_spec"
  {| forall l x. decr l x <: forall v. req l->v; ens l->v-x |}
;;

start_proof
  {|
    forall x y z.
      loop2 x y z <: forall a b. req b>=0; req y->a * z->b; ens y->(a+b*.x) * z->0
|}
;;

forall_intro ();;
forall_intro ();;
intro_pure "Hb";;
revert "a";;
induction ~name:"IH" (`Int 0) "b";; (* seems unsafe here?! *)
forall_intro ();;
goal_is {| loop2 x y z <: req y->a * z->b; ens y->a+b*.x * z->0 |};;
unfold "loop2";;
forall_elim ["b"];;
case ~name:"Hb_gt" "b > 0";;

(* case b > 0 *)
conj_elim_l ();;
goal_is
  {|
       req z->b /\ b>0; ens z->b; incr y x; decr z 1; loop2 x y z
    <: req y->a * z->b; ens y->a+b*.x * z->0
  |}
;;
unmix ();;
req_pure_elim ();;
req_heap_intro ();;
req_heap_elim ();;
ens_heap_elim ();;
rewrite "incr_spec";;
forall_elim ["a"];;
simpl ();;
req_heap_elim ();;
ens_heap_elim ();;
rewrite "decr_spec";;
forall_elim ["b"];;
simpl ();;
req_heap_elim ();;
ens_heap_elim ();;
specialize "IH" ["b-1"];;
forward "IH";;
pure_solver ();;
forward "IH";;
pure_solver ();;
specialize "IH" ["a+x"];;
rewrite "IH";;
req_heap_elim ();;
ens_heap_elim ();;
ens_heap_intro ();;
refl ();;

(* case b <= 0 *)
conj_elim_r ();;
goal_is
  {|
       req z->b /\ b<=0; ens z->b
    <: req y->a * z->b; ens y->a+b*.x * z->0
  |};;
unmix ();;
req_pure_elim ();;
req_heap_intro ();;
req_heap_elim ();;
ens_heap_elim ();;
ens_heap_intro ();;
refl ();;
qed ();;

Options.fail_fast := false;;
