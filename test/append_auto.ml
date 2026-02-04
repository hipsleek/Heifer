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
    (forall f. (fun x -> f x) <: f) =>
    forall xs k.
      (forall r. reset (k r) <: k r) =>
      reset (append_sh xs; r. k r) <: append_cps xs k
  |}
;;

intro_pure "eta_reduce";;
forall_intro ();;
revert "k";;
induction ~name:"IH" `List "xs";;
forall_intro ();;
intro_pure "Hk";;
unfold "append_sh";;
unfold "append_cps";;
shift_reset_reduce ();;
simple ();;
qed ();;

Options.fail_fast := false;;
