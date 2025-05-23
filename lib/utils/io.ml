let rec input_lines chan =
  try
    let line = input_line chan in
    let rest = input_lines chan in
    line :: rest
  with
    End_of_file -> []
