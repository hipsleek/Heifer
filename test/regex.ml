open Heifer.Interactive;;

axiom ~name:"eta_reduce"
  {| forall f. (fun x -> f x) <: f |}
;;

axiom ~name:"bind_id_r"
  {| forall t. t; x. x <: t |}
;;
