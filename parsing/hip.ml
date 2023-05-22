let () =
  if Unix.isatty Unix.stdout then Hiplib.Pretty.colours := `Ansi;
  Hiplib.main ()