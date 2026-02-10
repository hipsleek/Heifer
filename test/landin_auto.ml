open Heifer.Interactive;;

Options.fail_fast := true;;
Options.ignore_why3_failure := true;;

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
ens_heap_elim ();;
revert_heap ~side:`Rhs ();;
goal_is {| factf g n <: req l-> g; fact n |};;
rewrite "Hg";;
induction ~name:"IH" (`Int 0) "n";;
unfold ~side:`Lhs "factf";;
(* dbg_simple ();; *)
let c = simple2 ();;
Format.printf "%a@." Prover.Automation.pp_cert (Option.get c);;
qed ();;

Options.fail_fast := false;;
Options.ignore_why3_failure := false;;
(* Statistics.report ();; *)
