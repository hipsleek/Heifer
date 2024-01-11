
(* https://github.com/FabianWolff/closure-examples/blob/master/delegation.rs *)

let f y h g (* FIXME *)
(*@ ex yv; req y->yv; ens y->4 @*)
= let x = ref 3 in
  y := 4;
  (* Ensure that h and g are called successfully *)
  h (); g ()

let delegation_example () (* FIXME *)
(*@ ex x; ex y; req x->42*y->0; ens x->43*y->4 @*)
= let h () = 0 in
  let x = ref 42 in
  let g ()
  (* Captures x in the above line *)
  = x := !x + 1; 0 in
  let y = ref 0 in

  f y h g;
