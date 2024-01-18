
let entails_exists env left ex right =
  match Sys.getenv_opt "PROVER" with
  | Some "WHY3" -> Prover_why3.entails_exists env left ex right
  | Some "Z3" -> Prover_z3.entails_exists env left ex right
  | Some _ | None ->
    if !Hipcore.Globals.using_pure_fns then
      Prover_z3.entails_exists env left ex right
    else
      Prover_why3.entails_exists env left ex right

let handle f = f ()
