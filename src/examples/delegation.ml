
let f y h g (* FIXME *)
(*@ ex yv; req y->yv; ens y->4 @*)
= let x = ref 3 in
  y := 4;
  h (); g ()

let delegation_example ()
(*@ ex x; ex y; req x->42*y->0; ens x->42*y->4 @*)
= let h v = 0 in
  let x = ref 42 in
  let g v
  (* Captures x in the above line *)
  = x := !x + 1; 0 in
  let y = ref 0 in

  f y h g
