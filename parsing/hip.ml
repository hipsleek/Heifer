let () =
  if Unix.isatty Unix.stdout then Hiplib.Pretty.colours := `Ansi;
  Hiplib.Pretty.(debug_level :=
    Option.bind (Sys.getenv_opt "DEBUG") int_of_string_opt
    |> Option.value ~default:0);
  Hiplib.main ()