open Heifer.Interactive;;

declare
  {| append_sh xs =
    ens xs=[]; shift k k
    \/ ex x ys. ens xs=x::ys; append_sh ys; r. x::r
  |}
;;

declare
  {| append_cps xs k =
    ens xs=[]; k []
    \/ ex x ys. ens xs=x::ys; append_cps ys (fun r -> k (x::r))
  |}
;;

(* TODO use why3 append *)
declare
  {| append_pure xs ys =
    ens xs=[]; ys
    \/ ex x ys. ens xs=x::ys; append_pure xs ys
  |}
;;

declare {| append_delim xs ys =
    reset (append_sh xs); f. f ys
  |};;

(* start_proof
  {| forall xs ys. is_list xs => is_list ys =>
     reset (append_sh xs); r. zs ++ r
  <: append_pure xs ys
|}
;; *)

start_proof
  {| forall xs ys. is_list xs => is_list ys =>
     append_delim xs ys
  <: append_pure xs ys
|}
;;

unfold "append_delim";;
forall_intro ();;
intro_pure "Htx";;
intro_pure "Hty";;
unfold "append_sh";;
shift_reset_reduce ();;
simpl ();;
disj_elim ();;
admit ()
