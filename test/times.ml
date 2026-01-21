open Heifer.Interactive;;

declare
  {| times xs =
    ens xs=[]; 1
    \/ ex ys. ens xs=0::ys; shift k 0
    \/ ex x ys. ens xs=x::ys; times ys; r. x*.r
  |}
;;

declare
  {| times_pure xs =
    ens xs=[]; 1
    \/ ex x ys. ens xs=x::ys; times_pure ys; r. x*.r
  |}
;;

start_proof
  {| forall xs. is_list xs =>
     reset (times xs)
  <: times_pure xs
|}
