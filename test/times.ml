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

(* This axiom cannot be proven at the moment. Why?

   After `unfold "times_pure"` ans `simpl`, we need to prove that:
   `t <: ens xs=[]; ... \/ exists x xs'. ens xs=x::xs'; ...`
   To proceed, we need either xs=[] or xs=x::xs' for some x and xs'.
   But we have neither.

   This can be proven if we have "case analysis scheme" for list:
   `is_list xs => xs=[] \/ exists x xs'. xs=x::xs' /\ is_list xs'`
   We then need to add this hypothesis to all lemmas.

   Another option is to define times_pure using req and conj:
   ```
   times_pure xs =
     req xs=[]; 1 /\
     forall x xs'. req xs=x::xs'; times_pure xs'; r. r x*.r
   ```
   Then, after unfolding and simplifying, we can immediately introduce
   the assumption that either xs=[], or xs=x::xs', and proceed.
 *)
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
disj_elim ();;

left ();;
rewrite "Hk";;
refl ();;

right ();;
exists_elim ();
exists_intro ["x"; "xs'"];;
intro_pure "Hxs";;
elim_pure ();;
disj_elim ();;

left ();;
refl ();;

right ();;
simpl ();;
rewrite "IH";;
pure_solver ();;

forall_intro ();;
simpl ();;
rewrite "Hk";;
refl ();;

refl ();;
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
simpl ();;
disj_elim ();;

left ();;
refl ();;

right ();;
exists_elim ();;
exists_intro ["x"; "xs'"];;
intro_pure "Hxs";;
elim_pure ();;
disj_elim ();;

intro_pure "Hx";;
rewrite "Hx";;
rewrite "mult_0_l";;
rewrite ~direction:`Rtl "Hk";;
goal_is "0 <: times_pure xs'; r. 0";;
rewrite ~direction:`Rtl "times_pure_const_r";;
refl ();;

rewrite "IH";;
pure_solver ();;

simpl ();;
rewrite "mult_0_r";;
rewrite "Hk";;
refl ();;

simpl ();;
refl ();;
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
