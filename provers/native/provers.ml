
let entails_exists env left ex right =
  match Sys.getenv_opt "WHY3" with
  | None -> Prover_z3.entails_exists env left ex right
  | Some _ -> Prover_why3.entails_exists env left ex right

let handle f = f ()
