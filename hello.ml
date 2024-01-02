
let test25_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret