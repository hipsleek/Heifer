
(* let test25_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret *)

let test10 ()
  (*@ Norm(emp, 0) @*) =
  0
(* implicit normal stage *)