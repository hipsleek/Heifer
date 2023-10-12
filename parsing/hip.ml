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
  Hiplib.main ()