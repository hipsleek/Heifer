open Brr
open Hipcore.Common
open Hipcore_typed
open Typedhip

let ready () =
  Provers.handle (fun () ->
      let r =
        let open Syntax in
        Provers.entails_exists (SMap.empty) True [] (Atomic (EQ, num 3, plus (num 1) (num 1)))
      in
      Console.(log [str (Format.asprintf "test z3: 1+1=3 valid? %s@." (Provers_common.string_of_prover_result r))]);
      ())

let main () =
  Hipcore_typed.Pretty.colours := `Html;
  (* Console.(log [str "DOM content loaded."]); *)
  Jv.set Jv.global "ocaml_ready" (Jv.callback ~arity:1 ready);
  Jv.set Jv.global "hip_run_string"
    (Jv.callback ~arity:1 (fun s ->
         let debug = Jv.call Jv.global "debug_output" [||] |> Jv.to_bool in
         Hiplib.Debug.Query.user_query := if debug then [(Show, LogLevel 2, false)] else [(Hide, All, false)];
         Hiplib.run_string `Ocaml (Jv.to_string s)))

let () = main ()
