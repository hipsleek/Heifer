open Heifer.Interactive;;

Options.fail_fast := true;;

declare
  {|
    iter f xs =
      ens xs=[]; () \/
      ex x xs'. ens xs=x::xs'; f x; iter f xs'
  |}
;;

declare
  {| yield x = shift k (x::k) |}
;;

declare
  {| invert xs = reset (iter yield xs; []) |}
;;

declare
  {|
    to_seq xs =
      ens xs=[]; [] \/
      ex x xs'. ens xs=x::xs'; x::(fun _ -> to_seq xs')
  |}
;;

start_proof {| forall xs. invert xs <: to_seq xs |};;
forall_intro ();;
unfold "invert";;
induction ~name:"IH" `List "xs";;
unfold "iter";;
unfold "to_seq";;
shift_reset_reduce ();;
disj_elim ();;

left ();;
refl ();;

right ();;
exists_elim ();;
exists_intro ["x"; "xs'"];;
intro_pure "Hxs";;
elim_pure ();;
unfold "yield";;
shift_reset_reduce ();;
rewrite "IH";;
pure_solver ();;
refl ();;

qed ();;

Options.fail_fast := false;;
