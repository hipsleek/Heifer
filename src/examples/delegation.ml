
(* https://github.com/FabianWolff/closure-examples/blob/master/delegation.rs *)

let f y h g (* FIXME *)
(*@
  ex yv;
  req y->yv
    (* Ensures that h and g do not change anything on the heap *)
    /\ h <: (fun v r -> req T; ens T/\res=r)
    /\ g <: (fun v r -> req T; ens T/\res=r);
  ens y->4
@*)
(**
  The specification requires that:
  - Preconditions of h and g initially hold
  - Assignment to x does not interfere with the preconditions of h and g
  - h and g does not capture y and the assignment to y is guaranteed to be
    non-interfering
  - Invoking h does not interfere with the precondition of g
  (with reference from Example 10 from Specification and verification of closures)
*)
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
