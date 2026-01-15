
```ocaml
open Heifer.Interactive
```

```ocaml
declare {|foldr f init xs =
  ens xs=[]; init
  \/ ex h t. ens xs=h::t; foldr f init t; r. f h r|}
```

```ocaml
# start_proof "forall xs. foldr (fun c t -> c + t) 0 xs <: sum xs"

----------------------------------------
forall xs. foldr (fun c t -> c+t) 0 xs <: sum xs

- : unit = ()
```

<!--


forall_intro ();;
induction ~name:"IH" `List "xs";;
unfold "foldr";;
disj_elim ();;

(* base case *)
intro_pure "H";
prove ();;

(* inductive case *)
exists_elim ();;
intro_pure "Hxs";;
rewrite "IH";;

(* immediately discharge subgoal *)
prove ();;

simpl ();;
prove ();; -->
