open Brr
open Types

let ready () =
  Provers.handle (fun () ->
      let r = Provers.askZ3 (Not (Atomic (EQ, Num 3, Plus (Num 1, Num 1)))) in
      Console.(log [str (Format.asprintf "valid? %b@." (not r))]);
      ())

let main () =
  Console.(log [str "DOM content loaded."]);
  Jv.set Jv.global "ocaml_ready" (Jv.callback ~arity:1 ready)

let () = main ()
