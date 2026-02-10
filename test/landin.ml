open Heifer.Interactive;;

Options.fail_fast := true;;

declare
  {|
    landin_rec f =
      exists l g.
        ens l->();
        ens g=(fun n -> forall h. req l->h; ens l->h; f h n);
        forall v. req l->v; ens l->g;
        g
  |}
;;

declare
  {|
    factf self n =
      ens n=0; 1 \/
      ens n>0; self (n-1); r. n*.r
  |}
;;

start_proof
  {|
    forall n. landin_rec factf; f. f n <: fact n
  |}
;;
forall_intro ();;
unfold "landin_rec";;
simpl ();;
exists_elim ();;
ens_heap_elim ();;
intro_pure "Hg";;
forall_elim ["()"];;
req_heap_elim ();;
ens_heap_elim ();;
rewrite "Hg";;
simpl ();;
forall_elim ["g"];;
req_heap_elim ();;
goal_is {| ens l->g; factf g n <: fact n |};;
induction ~name:"IH" (`Int 0) "n";;
unfold "factf";;
intro_heap ();;
disj_elim ();;

(* base case *)
goal_is {| ens n=0; 1 <: fact n |};;
intro_pure "Hn";;
prove ();;

(* inductive case *)
goal_is {| ens n>0; g (n-1); r. n*.r <: fact n |};;
intro_pure "Hn";;
rewrite "Hg";;
simpl ();;
forall_elim ["g"];;
req_heap_elim ();;
rewrite "IH";;

pure_solver ();;

prove ();;
qed ();;

Options.fail_fast := false;;
