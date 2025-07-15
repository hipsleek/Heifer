open Brr
open Hipcore
open Hiptypes

let ready () =
  Provers.handle (fun () ->
      (* let r =
        Hiplib.ProversEx.is_valid True (Atomic (EQ, Num 3, Plus (Num 1, Num 1)))
      in
      Console.(log [str (Format.asprintf "test z3: 1+1=3 valid? %b@." r)]); *)
      ())

let main () =
  Hiplib.Pretty.colours := `Html;
  (* Console.(log [str "DOM content loaded."]); *)
  Jv.set Jv.global "ocaml_ready" (Jv.callback ~arity:1 ready);
  Jv.set Jv.global "hip_run_string"
    (Jv.callback ~arity:1 (fun s ->
         let debug = Jv.call Jv.global "debug_output" [||] |> Jv.to_bool in
         Hiplib.Debug.Query.user_query := if debug then [(Show, LogLevel 2, false)] else [(Hide, All, false)];
         Hiplib.run_string `Ocaml (Jv.to_string s)))

let () = main ()
