let () =
  if Unix.isatty Unix.stdout then Hiplib.Pretty.colours := `Ansi;
  Hiplib.Common.(debug_level :=
    Option.bind (Sys.getenv_opt "DEBUG") int_of_string_opt
    |> Option.value ~default:dbg_none);
  Hiplib.main ()