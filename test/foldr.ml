open Heifer.Interactive;;

declare
  {|foldr f init xs =
  ens xs=[]; init
  \/ ex h t. ens xs=h::t; foldr f init t; r. f h r|}
;;

start_proof "forall xs. foldr (fun c t -> c + t) 0 xs <: sum xs";;
forall_intro ();;
induction ~name:"IH" `List "xs";;
unfold "foldr";;
disj_elim ();;
intro_pure "H";;
prove ();;
exists_elim ();;
intro_pure "Hxs";;
rewrite "IH";;
prove ();;
simpl ();;
prove ()
