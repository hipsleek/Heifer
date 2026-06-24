open Heifer.Interactive;;

Options.fail_fast := true;;

declare
  {|
    countdown_loop get set =
      get (); v.
      ens v>0;
      set (v-1);
      countdown_loop get set
  |}
;;

declare
  {| countdown get set n = set n; countdown_loop get set |}
;;

declare
  {| get1 _ = shift k (fun s -> k s; f. f s) |}
;;

declare
  {| set1 s = shift k (fun _ -> k (); f. f s) |}
;;

declare
  {|
    run_countdown1 n =
      reset (countdown get1 set1 n; fun _ -> ()); f.
      f 0
    |}
;;

declare
  {| get2 r = fun _ -> exists s. ens r->s; req r->s; s |}
;;

declare
  {| set2 r = fun s -> exists _. ens r->_; req r->s |}
;;

declare
  {|
    run_countdown2 n =
      forall r. req r->0;
      get2 r; get.
      set2 r; set.
      countdown get set n
  |}
;;

start_proof {| forall n. is_int n => run_countdown1 n <: run_countdown2 n |};;
forall_intro ();;
intro_pure "Hn";;
unfold "run_countdown1";;
unfold "run_countdown2";;
unfold "countdown";;
forall_intro ();;
intro_heap ();;
unfold "set1";;
shift_reset_reduce ();;
simpl ();;
simpl ();;
unfold "get2";;
unfold "set2";;
simpl ();;
simpl ();;
exists_intro ["0"];;
elim_heap ();;
induction ~name:"IH" (`Int 0) "n";;
intro_heap ();;
unfold "countdown_loop";;
simpl ();;
exists_intro ["n"];;
elim_heap ();;
intro_heap ();;
unfold "get1";;
shift_reset_reduce ();;
simpl ();;
simpl ();;
shift_reset_reduce ();;
simpl ();;
intro_pure "Hgt";;
elim_pure ();;
exists_intro ["n"];;
elim_heap ();;
intro_heap ();;
unfold "set1";;
shift_reset_reduce ();;
simpl ();;
simpl ();;
rewrite "IH";;
pure_solver ();;
pure_solver ();;
elim_heap ();;
refl ();;
qed ();;

Options.fail_fast := false;;
