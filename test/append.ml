open Heifer.Interactive;;

Options.fail_fast := true;;

axiom ~name:"eta_reduce"
  {| forall f. (fun x -> f x) <: f |}
;;

axiom ~name:"bind_id_r"
  {| forall t. t; x. x <: t |}
;;

declare
  {|
    append_sh xs =
      ens xs=[]; shift k k \/
      exists x xs'. ens xs=x::xs'; append_sh xs'; r. x::r
  |}
;;

axiom ~name:"append_sh_bind_id_r"
  {| forall xs. append_sh xs <: append_sh xs; x. x |}
;;

declare
  {| append_delim xs ys = reset (append_sh xs); f. f ys |}
;;

declare
  {|
    append_cps xs k =
      ens xs=[]; k \/
      exists x xs'. ens xs=x::xs'; append_cps xs' (fun r -> k (x::r))
  |}
;;

declare
  {|
    append_pure xs ys =
      ens xs=[]; ys \/
      exists x xs'. ens xs=x::xs'; append_pure xs' ys; r. x::r
  |}
;;

lemma ~name:"append_sh/append_cps"
  {|
    forall xs k.
      (forall r. reset (k r) <: k r) =>
      reset (append_sh xs; r. k r) <: append_cps xs k
  |}
;;

forall_intro ();;
revert "k";;
induction ~name:"IH" `List "xs";;
forall_intro ();;
intro_pure "Hk";;
unfold "append_sh";;
unfold "append_cps";;
shift_reset_reduce ();;
disj_elim ();;

left ();;
intro_pure "Hxs";;
elim_pure ();;
rewrite "Hk";;
rewrite "eta_reduce";;
refl ();;

right ();;
exists_elim ();
exists_intro ["x"; "xs'"];;
intro_pure "Hxs";;
elim_pure ();;
simpl ();;
rewrite "IH";;

pure_solver ();;

forall_intro ();;
simpl ();;
rewrite "Hk";;
refl();;

refl ();;
qed ();;

lemma ~name:"append_cps/append_pure"
  {|
    forall xs ys k.
      append_cps xs k; f. f ys <: append_pure xs ys; r. k r
  |}
;;

forall_intro ();;
revert "k";;
induction ~name:"IH" `List "xs";;
forall_intro ();;
unfold "append_cps";;
unfold "append_pure";;
simpl ();;
disj_elim ();;

left ();;
refl ();;

right ();;
exists_elim ();;
exists_intro ["x"; "xs'"];;
intro_pure "Hxs";;
elim_pure ();;
rewrite "IH";;

pure_solver ();;

simpl ();;
refl ();;
qed ();;

start_proof
  {| forall xs ys. append_delim xs ys <: append_pure xs ys |}
;;

forall_intro ();;
unfold "append_delim";;
rewrite "append_sh_bind_id_r";;
rewrite "append_sh/append_cps";;

forall_intro ();;
simpl ();;
shift_reset_reduce ();;
refl ();;

rewrite "append_cps/append_pure";;
simpl ();;
rewrite "bind_id_r";;
refl ();;
qed ();;

Options.fail_fast := false;;
