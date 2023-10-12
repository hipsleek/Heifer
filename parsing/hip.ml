
let redirect_stdout f =
  let oldstdout = Unix.dup Unix.stdout in
  let newstdout = open_out "out.txt" in
  Unix.dup2 (Unix.descr_of_out_channel newstdout) Unix.stdout;
  f ();
  flush stdout;
  Unix.dup2 oldstdout Unix.stdout;
  Unix.close oldstdout;
  close_out newstdout

let () =
  Hiplib.Pretty.(debug_level :=
    Option.bind (Sys.getenv_opt "DEBUG") int_of_string_opt
    |> Option.value ~default:0);
  Hiplib.(test_mode :=
    (Option.bind (Sys.getenv_opt "TEST") int_of_string_opt
    |> Option.value ~default:0) > 0);
  Hiplib.(file_mode :=
    (Option.bind (Sys.getenv_opt "FILE") int_of_string_opt
    |> Option.value ~default:0) > 0);
  if Unix.isatty Unix.stdout && not !Hiplib.file_mode then
    Hiplib.Pretty.colours := `Ansi;
  if !Hiplib.file_mode then
    redirect_stdout Hiplib.main
  else
    Hiplib.main ()