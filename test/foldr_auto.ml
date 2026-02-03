open Heifer.Interactive;;

(* First, a definition of `foldr`. *)

Options.fail_fast := true;;

declare
  {|
    foldr f acc xs =
      ens xs=[]; acc \/
      ex x xs'. ens xs=x::xs'; foldr f acc xs'; r. f x r
  |}
;;

start_proof {| forall xs. is_int_list xs => foldr (fun x acc -> x + acc) 0 xs <: sum xs |};;
forall_intro ();;
intro_pure "Hty";;
goal_is "foldr (fun x acc -> x+acc) 0 xs <: sum xs";;

(* We proceed by induction on the structure of the list `xs`. *)
induction ~name:"IH" `List "xs";;
unfold "foldr";;

goal_is
  {|
    ens xs=[]; 0 \/
    (ex x xs'.
      ens xs=x::xs';
      foldr (fun x1 acc -> x1+acc) 0 xs'; r. (fun x1 acc -> x1+acc) x r)
    <: sum xs
  |}
;;

simple ()
