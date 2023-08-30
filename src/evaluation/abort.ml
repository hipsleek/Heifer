effect Zero : unit

let client () 
(*@ ex r; Zero(emp, (), r); req false/\emp; ex r1; Norm(false/\emp, r1) @*)
=
  perform (Zero ());
  assert false

let handler ()
(*@ ex r; Norm(r=3/\emp, r) @*)
=
  match client () with
  | v -> 2
  | effect Zero k -> 3

let invalid_false ()
(*@ ex r; Norm(false/\emp, r) @*)
=
  match client () with
  | v -> 2
  | effect Zero k -> continue k ()