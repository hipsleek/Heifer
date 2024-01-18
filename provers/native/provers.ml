
let entails_exists env left ex right =
  match Sys.getenv_opt "PROVER" with
  | Some "WHY3" -> Prover_why3.entails_exists env left ex right
  | Some "Z3" -> Prover_z3.entails_exists env left ex right
  | Some _ | None ->
    let needs_why3 =
      (* if no pure functions are used, short circuit immediately.
         otherwise, switch only if some part of the formula needs why3 *)
      !Hipcore.Globals.using_pure_fns &&
        (Hipcore.Subst.needs_why3#visit_pi () left ||
        Hipcore.Subst.needs_why3#visit_pi () right)
    in
    if needs_why3 then
      Prover_why3.entails_exists env left ex right
    else
      Prover_z3.entails_exists env left ex right

let handle f = f ()
