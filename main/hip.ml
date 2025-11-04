
open Cmdliner
open Cmdliner.Term.Syntax

let redirect_stdout f =
  let name = "out.org" in
  Format.printf "%s@." name;
  let oldstdout = Unix.dup Unix.stdout in
  let newstdout = open_out name in
  Unix.dup2 (Unix.descr_of_out_channel newstdout) Unix.stdout;
  f ();
  flush stdout;
  Unix.dup2 oldstdout Unix.stdout;
  Unix.close oldstdout;
  close_out newstdout

let in_test_mode =
  let env = Cmd.Env.info "TEST" in
  let doc = "Run in test mode." in
  Arg.(value & flag & info ["test"] ~env ~doc ~docv:"TEST")

let output_to_file =
  let env = Cmd.Env.info "FILE" in
  let doc = "Redirect all output to a file." in
  Arg.(value & flag & info ["debug-file"] ~env ~doc ~docv:"DEBUG_FILE")

let file_to_prove =
  let doc = "The file with code to verify." in
  Arg.(required & pos 0 (some string) None & info [] ~doc ~docv:"FILE")

let show_types =
  let env = Cmd.Env.info "SHOW_TYPES" in
  let doc = "Insert type annotations in output." in
  Arg.(value & flag & info ["show-types"] ~env ~doc ~docv:"SHOW_TYPES")

let perfetto_trace =
  let env = Cmd.Env.info "CTF" in
  let doc = "Output a trace file viewable by Perfetto." in
  Arg.(value & flag & info ["perfetto-trace"] ~env ~doc ~docv:"TRACE")

let debug_query =
  let env = Cmd.Env.info "DEBUG" in
  let doc = "Enable and specify parameters to filter debug output." in
  Arg.(value & opt (some string) None & info ["debug"] ~env ~doc ~docv:"DEBUG")

let run_as_untyped =
  let env = Cmd.Env.info "NOTYPES" in
  let doc = "Ignore types when proving" in
  Arg.(value & flag & info ["notypes"] ~env ~doc ~docv:"DEBUG")

let certificate_file =
  let doc = "Output a Rocq certificate of any proved entailment. (Experimental)" in
  Arg.(value & opt (some string) None & info ["certificate"] ~doc ~docv:"CERT_FILE")

let cmd =
  Cmd.make (Cmd.info "heifer" ~version:"0.1") @@
  let+ file_to_prove and+ in_test_mode and+ output_to_file
    and+ show_types and+ perfetto_trace and+ debug_query
    and+ run_as_untyped and+ certificate_file in
  Hiplib.test_mode := in_test_mode;
  Hiplib.file_mode := output_to_file;
  if show_types then
    Hipcore_typed.Pretty.(set_current_config set_types_display);
  if run_as_untyped then
    Hipcore_typed.Dynamic_typing.set_dynamic_typing ();
  Hiplib.Debug.init ~ctf:perfetto_trace ~org:!Hiplib.file_mode debug_query;
  let file_to_prove = Sys.getcwd () ^ "/" ^ file_to_prove in
  begin
  if !Hiplib.file_mode then
    redirect_stdout (fun () -> Hiplib.run_file ~certificate_file file_to_prove)
  else 
    Hiplib.run_file ~certificate_file file_to_prove
  end;
  if !Hiplib.test_mode && not !Hiplib.tests_failed then Format.printf "ALL OK!@.";
  let return_code = if !Hiplib.tests_failed then 1 else 0 in
  return_code

let main () = Cmd.eval' cmd

let () = if !Sys.interactive then () else exit (main ())
