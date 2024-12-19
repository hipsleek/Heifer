
(* let test_ab ()
(*@ ex r; A(emp, r); ex r1; B(emp, r1); Norm(emp, 1) @*)
= perform A; perform B; 1 *)

let test_a ()
(*@ ex r; A(emp, r); Norm(emp, 1) @*)
= perform A; 1

(* let handler_unhandled ()
(*@ ex r; A(emp, r); Norm(emp, 1) @*)
=
  match test_a () with
  | effect B k -> 2
  | v -> v

let handler_unhandled_1 ()
(*@ ex r; A(emp, r); Norm(emp, 1) @*)
=
  match test_ab () with
  | effect B k -> 2
  | v -> v

let handler_zero ()
(*@ Norm(emp, 2) @*)
=
  match test_a () with
  | effect A k -> 2
  | v -> v

let handler_a ()
(*@ Norm(emp, 1) @*)
=
  match test_a () with
  | effect A k -> continue k ()
  | v -> v

let handler_ab ()
(*@ Norm(emp, 1) @*)
=
  match test_ab () with
  | effect A k -> continue k ()
  | effect B k -> continue k ()
  | v -> v *)

let handler_multi ()
(*@ Norm(emp, 2) @*)
=
  match test_a () with
  | effect A k ->
    continue k () + continue k ()
  | v -> v
