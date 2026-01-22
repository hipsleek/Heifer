open Heifer.Interactive;;

declare
  {|
  landin_rec f =
    ex l knot.
      ens l->();
      ens knot=(fun n -> forall f1. req l->f1; ens l->f1; f f1 n);
      forall v0. req l->v0; ens l->knot;
      knot
|}
;;

declare {|
  factf self n =
    ens n=0; 1
    \/ ens n>0; self (n-1); r1. n*.r1
|};;

start_proof {|
  forall n. is_int n =>
    landin_rec factf; f. f n <: ex l v. ens l->v; fact n
|};;

(* Options.notation := false;; *)
forall_intro ();;
intro_pure "Hty";;
unfold "landin_rec";;

goal_is
  {|
     (ex l knot.
        ens l->();
        ens knot=(fun n1 ->
                   forall f1.
                     req l->f1; ens l->f1; factf f1 n1);
        (forall v0. req l->v0; ens l->knot; knot)); f.
       f n
  <: ex l v. ens l->v; fact n
        |}
;;

exists_elim ();;
simpl ();;
intro_heap ();;
intro_pure "Hknot";;

(* TODO lemmas *)
(* deal with the read *)
forall_elim ["()"];;
simpl ();;
req_heap_elim ();;
simpl ();;

goal_is {|
     ens l->knot; knot n
  <: ex l v. ens l->v; fact n
|};;

induction ~name:"IH" (`Int 0) "n";;

(* TODO rewrite at one occurrence, currently worked around by introing *)
intro_heap ();;
rewrite "Hknot";;

goal_is
  {|
     (fun n1 -> forall f1. req l->f1; ens l->f1; factf f1 n1)
       n
  <: ex l v. ens l->v; fact n
|}
;;

simpl ();;
forall_elim ["knot"];;
req_heap_elim ();;
intro_heap ();;

(* now we can get at the structure of factf *)

unfold "factf";;
disj_elim ();;

(* base case *)
goal_is {|
  ens n=0; 1
  <: ex l v. ens l->v; fact n
|};;

intro_pure "Hn";;
exists_intro ["l"; "knot"];;
ens_heap_intro ();;

(* Options.show_why3_goal := true;; *)
prove ();;

(* inductive case *)
goal_is {|
  ens n>0; knot (n-1); r1. n*.r1
  <: ex l v. ens l->v; fact n
|};;

intro_pure "Hn";;
revert_heap ();;
rewrite "IH";;
prove ();;
prove ();;
goal_is "(ex l v. ens l->v; fact (n-1)); r1. n*.r1 <: ex l v. ens l->v; fact n";;
exists_elim ();;
exists_intro ["l1"; "v"];;
simpl ();;
intro_heap ();;
ens_heap_intro ();;

(* Prover.Tactic.Options.show_why3_goal := true;; *)

Options.show_why3_goal := true;;
prove ();;

(* TODO a defn of fact, some way to include it in here *)

qed ()
