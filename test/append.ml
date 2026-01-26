open Heifer.Interactive;;

declare
  {| append_sh xs =
    ens xs=[]; shift k k
    \/ ex x ys. ens xs=x::ys; append_sh ys; r. x::r
  |}
;;

declare
  {| append_cps xs k =
    ens xs=[]; k
    \/ ex x ys. ens xs=x::ys; append_cps ys (fun r -> k (x::r))
  |}
;;

axiom ~name:"eta_reduction" {| forall f. (fun x -> f x) <: f |}
;;

(* TODO use why3 append *)
(* declare
  {| append_pure xs ys =
    ens xs=[]; ys
    \/ ex x ys. ens xs=x::ys; append_pure xs ys
  |}
;;

declare {| append_delim xs ys =
    reset (append_sh xs); f. f ys
  |};; *)

(* start_proof
  {| forall xs ys. is_list xs => is_list ys =>
     reset (append_sh xs); r. zs ++ r
  <: append_pure xs ys
|}
;; *)

start_proof
  {|  forall xs k.
        (forall r. reset (k r) <: k r) =>
        reset(append_sh xs; r. k r) <: append_cps xs k
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
ens_pure_intro ();;
rewrite "Hk";;
rewrite "eta_reduction";;
refl ();;

right ();;
exists_elim ();
exists_intro ["x"; "ys"];;
intro_pure "Hxs";;
ens_pure_intro ();;
simpl ();;
rewrite "IH";;

admit ();;

forall_intro ();;
simpl ();;
rewrite "Hk";;
refl();;

refl ();;
qed ();;

(*
start_proof
  {| forall xs ys. is_int_list xs => is_int_list ys =>
     append_delim xs ys
  <: append_pure xs ys
|}
;;

unfold "append_delim";;
forall_intro ();;
intro_pure "Hty_xs";;
intro_pure "Hty_ys";;
unfold "append_sh";;
shift_reset_reduce ();;
simpl ();;
disj_elim ();;

admit ();;

exists_elim ();;
simpl ();;
intro_pure "Hxs";;
*)
