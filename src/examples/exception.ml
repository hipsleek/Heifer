
let failing x
(*@ ex i; req x->i; ex r; E(x->i+1 /\ x=3, r)
  \/
   ex i; req x->i; ens x->i+1 /\ res=i+1 /\ ~x=3 @*)
=
  x := !x + 1;
  if x = 3 then perform E else !x

(* TODO there is a bug in handler reasoning, result should be 1 *)

let main ()
(*@ ex y; ens y->3 /\ res=3 @*)
=
  let y = ref 2 in
  match failing y with
  | effect E k -> 1
  | v -> v