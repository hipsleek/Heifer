
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

let () =
  Hiplib.(test_mode :=
    (Option.bind (Sys.getenv_opt "TEST") int_of_string_opt
    |> Option.value ~default:0) > 0);
  Hiplib.(file_mode :=
    (Option.bind (Sys.getenv_opt "FILE") int_of_string_opt
    |> Option.value ~default:0) > 0);
  let ctf =
    Option.bind (Sys.getenv_opt "CTF") int_of_string_opt
    |> Option.value ~default:0 > 0
  in
  if Unix.isatty Unix.stdout && not !Hiplib.file_mode && not ctf then
    Hiplib.Pretty.colours := `Ansi;
  Hiplib.Debug.init ctf (Sys.getenv_opt "DEBUG") !Hiplib.file_mode;
  if !Hiplib.file_mode then
    redirect_stdout Hiplib.main
  else
    Hiplib.main ()
