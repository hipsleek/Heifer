open Heifer.Interactive;;

declare
  {| times xs =
    ens xs=[]; 1
    \/ (ex ys. ens xs=0::ys; shift k 0)
    \/ ex x ys. ens xs=x::ys; times ys; r. x*.r
  |}
;;

(* declare
  {| times_pure xs =
    ens xs=[]; 1
    \/ ex x ys. ens xs=x::ys; times_pure ys; r. x*.r
  |}
;; *)

start_proof
  {| forall xs x. is_int_list xs => is_int x =>
   reset (times xs; r. x*r)
<: product (x::xs)
|}
;;

forall_intro ();;
intro_pure "Htxs";;
revert "x";;
induction ~name:"IH" `List "xs";;

(* TODO *)

(* intro_pure "Htx";;
unfold "times";; *)

start_proof {| forall xs. is_int_list xs =>
     reset (times xs)
  <: product xs
|};;

forall_intro ();;
intro_pure "Hty";;
unfold "times";;
shift_reset_reduce ();;
disj_elim ();;
disj_elim ();;

(* base case *)
goal_is {|
   ens xs=[]; 1
<: product xs
|};;

intro_pure "Hxs";;
prove ();;

(* case 1 *)
goal_is {|
   (ex ys. ens xs=0::ys; 0)
<: product xs
|};;

exists_elim ();;
intro_pure "Hxs";;
prove ();;

(* case 2 *)

goal_is {|
   (ex x ys. ens xs=x::ys; reset (times ys; r. x*.r))
<: product xs
|};;

exists_elim ();;
intro_pure "Hxs"
