let test13 ()
(*@ ex a b.
   ens a->0 * b->1/\res=1
@*)
=
  let i = ref 0 in
  let j = ref 1 in
  1
