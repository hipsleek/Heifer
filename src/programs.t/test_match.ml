
let client ()
(*@ ex r; X(emp, r); Norm(emp, r) @*)
= perform X

let handler ()
(*@ Norm(emp, 1) @*)
=
  match client () with
  | effect X k (*@ Norm(emp, 1) @*) -> 1
  | v -> v