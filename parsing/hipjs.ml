open Brr
open Hiptypes

let ready () =
  Provers.handle (fun () ->
      let r = Provers.askZ3 (Not (Atomic (EQ, Num 3, Plus (Num 1, Num 1)))) in
      Console.(log [str (Format.asprintf "test z3: 1+1=3? %b@." (not r))]);
      ())

let main () =
  (* Console.(log [str "DOM content loaded."]); *)
  Jv.set Jv.global "ocaml_ready" (Jv.callback ~arity:1 ready);
  Jv.set Jv.global "hip_run_string"
    (Jv.callback ~arity:2 (fun inc s ->
         Hiplib.run_string ~js:true (Jv.to_bool inc) (Jv.to_string s)))

let () = main ()
