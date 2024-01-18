
open Hipcore
open Hiptypes

let cache : (pi * string list * pi, bool) Hashtbl.t = Hashtbl.create 10

let memo k f =
  match Hashtbl.find_opt cache k with
  | None ->
    let r = f () in
    Hashtbl.add cache k r;
    r
  | Some r -> r


let entails_exists env left ex right =
  let@ _ = memo (left, ex, right) in
  match Sys.getenv_opt "PROVER" with
  | Some "WHY3" -> Prover_why3.entails_exists env left ex right
  | Some "Z3" -> Prover_z3.entails_exists env left ex right
  | Some _ | None ->
    let needs_why3 =
      (* if no pure functions are used, short circuit immediately.
         otherwise, switch only if some part of the formula needs why3 *)
      !Globals.using_pure_fns &&
        (Subst.needs_why3#visit_pi () left ||
        Subst.needs_why3#visit_pi () right)
    in
    if needs_why3 then
      Prover_why3.entails_exists env left ex right
    else
      Prover_z3.entails_exists env left ex right

let handle f = f ()
