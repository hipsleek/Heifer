
open Hipcore
open Typedhip
open Common

let cache : (pi * string list * pi, Provers_common.prover_result) Hashtbl.t = Hashtbl.create 10

let memo k f =
  match Hashtbl.find_opt cache k with
  | None ->
    let r = f () in
    Hashtbl.add cache k r;
    r
  | Some r -> r

let needs_why3 =
  object
    inherit [_] reduce_spec
    method zero = false
    method plus = (||)

    method! visit_TApp () _f _a =
      true
  end

let entails_exists env left ex right =
  let@ _ = memo (left, ex, right) in
  let prove_why3 env left ex right = Prover_why3.entails_exists env (Untypehip.untype_pi left) ex (Untypehip.untype_pi right) in
  let prove_z3 env left ex right = Prover_z3.entails_exists env left ex right in
  let prover = match Sys.getenv_opt "PROVER" with
  | Some "WHY3" -> prove_why3
  | Some "Z3" -> prove_z3
  | Some _ | None ->
    let needs_why3 =
      (* if no pure functions are used, short circuit immediately.
         otherwise, switch only if some part of the formula needs why3 *)
      !Globals.using_pure_fns &&
        (needs_why3#visit_pi () left ||
        needs_why3#visit_pi () right)
    in
    if needs_why3 then
      prove_why3
    else
      prove_z3
  in
  prover env left ex right

let handle f = f ()
