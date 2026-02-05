open Heifer.Interactive;;

Options.fail_fast := true;;

axiom ~name:"mult_0_l"
  {| forall x. 0*.x = 0 |}
;;

axiom ~name:"mult_0_r"
  {| forall x. x*.0 = 0 |}
;;

axiom ~name:"bind_id_r"
  {| forall t. t; x. x <: t |}
;;

declare
  {|
    times_sh xs =
      ens xs=[]; 1 \/
      ex x xs'. ens xs=x::xs'; (ens x=0; shift k 0 \/ times_sh xs'; r. x*.r)
  |}
;;

declare
  {| times xs = reset (times_sh xs) |}
;;

declare
  {|
    times_cp xs k =
      ens xs=[]; k 1 \/
      ex x xs'. ens xs=x::xs'; (ens x=0; 0 \/ times_cp xs' (fun r -> k (x*.r)))
  |}
;;

declare
  {|
    times_pure xs =
      ens xs=[]; 1 \/
      ex x xs'. ens xs=x::xs'; times_pure xs'; r. x*.r
  |}
;;


lemma ~name:"times_sh/times_cp"
  {|
    forall xs k.
      (forall r. reset (k r) <: k r) =>
      reset (times_sh xs; r. k r) <: times_cp xs k
  |}
;;

forall_intro ();;
revert "k";;
induction ~name:"IH" `List "xs";;
forall_intro ();;
intro_pure "Hk";;
unfold "times_sh";;
unfold "times_cp";;
shift_reset_reduce ();;
simple ();;
qed ();;

Options.fail_fast := false;;
