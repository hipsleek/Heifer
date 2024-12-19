effect Zero : unit

let client () 
(*@ ex r; Zero(emp, r); req F; ens F @*)
=
  perform Zero;
  assert false

let handler ()
(*@ ex r; ens r=3/\res=r @*)
=
  match client () with
  | v -> 2
  | effect Zero k -> 3

let invalid_false ()
(*@ ens F @*)
=
  match client () with
  | v -> 2
  | effect Zero k -> continue k ()