let racket_regex = Str.regexp ".*\\.rkt$"

let get_file_type (file_name : string) : [`Ocaml | `Racket] =
  let is_racket_file = Str.string_match racket_regex file_name 0 in
  if is_racket_file then `Racket else `Ocaml

let rec input_lines chan =
  try
    let line = input_line chan in
    let rest = input_lines chan in
    line :: rest
  with
    End_of_file -> []
