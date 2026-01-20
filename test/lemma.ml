open Heifer.Interactive;;

start_proof {|
  (ex x. ens x->1; read x) <: 1
|};;

axiom ~name:"H" "forall x. read x <: forall v. req x->v; ens x->v; v";;
exists_elim ();;
rewrite "H";;
intro_heap ();;
forall_elim ["1"];;
req_heap_elim ();;
ens_heap_elim ();;
refl ();;
qed ()
