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
    forall n. landin_rec factf; f. f n <: exists l f. ens l->f; fact n
  |}
;;

forall_intro ();;
unfold "landin_rec";;
goal_is
  {|
    (exists l g.
      ens l->();
      ens g=(fun n1 -> forall h. req l->h; ens l->h; factf h n1);
      (forall v. req l->v; ens l->g; g)); f. f n
    <: exists l f. ens l->f; fact n
  |}
;;
exists_elim ();;
simpl ();;
ens_heap_elim ();;
intro_pure "Hg";;
forall_elim ["()"];;
simpl ();;
req_heap_elim ();;
ens_heap_elim ();;
rewrite "Hg";;
simpl ();;
forall_elim ["g"];;
req_heap_elim ();;
exists_intro ["l"; "g"];;
induction ~name:"IH" (`Int 0) "n";;
unfold "factf";;
intro_heap ();;
disj_elim ();;

(* base case *)
goal_is {| ens n=0; 1 <: ens l->g; fact n |};;
intro_pure "Hn";;
ens_heap_intro ();;
prove ();;

(* inductive case *)
goal_is {| ens n>0; g (n-1); r. n*.r <: ens l->g; fact n |};;
intro_pure "Hn";;
revert_heap ();;
rewrite "Hg";;
simpl ();;
rewrite ~direction:Direction.rtl "Hg";;
ens_heap_elim ();;
forall_elim ["g"];;
simpl ();;
req_heap_elim ();;
rewrite "IH";;

pure_solver ();;

simpl ();;
ens_heap_elim ();;
ens_heap_intro ();;
prove ();;
qed ();;

Options.fail_fast := false;;
