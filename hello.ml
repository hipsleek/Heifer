let test25_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret
(* this can be proved in why3 due to it leveraging type information - since ret is of type unit, its value must be (). our z3 encoding is wrong since we encode unit as int *)

let test12_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  1
(* this fails with a type error in why3, as it should *)
