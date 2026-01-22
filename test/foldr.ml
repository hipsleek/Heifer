open Heifer.Interactive;;

(* First, a definition of `foldr`. *)

declare {|foldr f init xs =
  ens xs=[]; init
  \/ ex h t. ens xs=h::t; foldr f init t; r. f h r|};;

start_proof "forall xs. is_int_list xs => foldr (fun c t -> c + t) 0 xs <: sum xs";;
forall_intro ();;
intro_pure "Hty";;
goal_is "foldr (fun c t -> c+t) 0 xs <: sum xs";;

(* We proceed by induction on the structure of the list `xs`. *)
induction ~name:"IH" `List "xs";;
unfold "foldr";;

goal_is
  {|
   ens xs=[]; 0
   \/ (ex h t.
         ens xs=h::t;
         foldr (fun c t1 -> c+t1) 0 t; r.
           (fun c t1 -> c+t1) h r)
<: sum xs
|}
;;

disj_elim ();;

(* base case *)
goal_is "ens xs=[]; 0 <: sum xs";;
intro_pure "H";;
prove ();;

(* Inductive case *)

goal_is
  {|
   ex h t.
     ens xs=h::t;
     foldr (fun c t1 -> c+t1) 0 t; r.
       (fun c t1 -> c+t1) h r
<: sum xs
|}
;;

exists_elim ();;
intro_pure "Hxs";;

goal_is {|
   foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
<: sum xs
|};;

(* To use the induction hypothesis, we have to prove that `t` is a sublist of `xs`. This lets us rewrite the call to `foldr`. *)

rewrite "IH";;
prove ();;
prove ();;

goal_is {|
   sum t; r. (fun c t1 -> c+t1) h r
<: sum xs
|};;

(* Having done that, the goal follows from the definition of `sum`. *)

simpl ();;
Options.show_why3_goal := true;;
prove ();;
qed ()
