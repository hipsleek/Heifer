open Heifer.Interactive;;

Options.fail_fast := true;;
Options.ignore_why3_failure := true;;

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

axiom ~name:"times_sh_id_r"
  {| forall xs. times_sh xs <: times_sh xs; x. x |}
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

axiom ~name:"times_pure_const_r"
  {| forall xs t. t <: times_pure xs; r. t |}
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
(* simple ();; *)
let c = simple2 ();;
Format.printf "%a@." Prover.Automation.pp_cert (Option.get c);;
qed ();;


lemma ~name:"times_cp/times_pure"
  {|
    forall xs k.
      (0 <: k 0) =>
      times_cp xs k <: times_pure xs; r. k r
  |}
;;
forall_intro ();;
revert "k";;
induction ~name:"IH" `List "xs";;
forall_intro ();;
intro_pure "Hk";;
unfold "times_cp";;
unfold "times_pure";;
(* simple ();; *)
let c = simple2 ();;
Format.printf "%a@." Prover.Automation.pp_cert (Option.get c);;
qed ();;


start_proof
  {| forall xs. times xs <: times_pure xs |}
;;
forall_intro ();;
unfold "times";;
rewrite "times_sh_id_r";;
rewrite "times_sh/times_cp";;

forall_intro ();;
simpl ();;
shift_reset_reduce ();;
refl ();;

rewrite "times_cp/times_pure";;

simpl ();;
refl ();;

simpl ();;
rewrite "bind_id_r";;
refl ();;
qed ();;


Options.fail_fast := false;;
Options.ignore_why3_failure := false;;
(* Statistics.report ();; *)
