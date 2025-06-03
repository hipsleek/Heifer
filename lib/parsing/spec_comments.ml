(** Module for converting specification comments into OCaml AST attributes.

  The approach used here is very simple, and can probably be substituted for
  a complete lexer+parser if needed. *)

let spec_comment_begin = "(*@"

let spec_comment_end = "@*)"

let patterns = [(spec_comment_begin, "[@@spec {|"); (spec_comment_end, "|}]")]

let find_and_replace patterns string =
  let parsed = Queue.create () in
  let rec go start =
    if start < String.length string
    then
    let rec check_patterns patterns =
      match patterns with
      | [] -> 
          if start < String.length string
          then (Queue.push (String.make 1 string.[start]) parsed; 1)
          else 0
      | (pattern, replacement)::rest ->
          if start + String.length pattern <= String.length string && String.sub string start (String.length pattern) = pattern
          then (Queue.push replacement parsed; String.length pattern)
          else check_patterns rest
    in
    let chars_read = check_patterns patterns in
    if start + chars_read < String.length string
    then go (start + chars_read)
  in
  go 0;
  parsed |> Queue.to_seq |> List.of_seq |> String.concat ""
    
let parse_spec_comments code = find_and_replace patterns code

let%expect_test "test replacement" =
  let input = {|
  (** documentation comment *)
  let map xs f = match xs with
  | x::xs -> (f x)::(map xs f)
  | [] -> [] (* regular comment *)
  (*@ specification comment @*)
  |} in
  Printf.printf "%s" (parse_spec_comments input);
  [%expect {output|
    (** documentation comment *)
    let map xs f = match xs with
    | x::xs -> (f x)::(map xs f)
    | [] -> [] (* regular comment *)
    [@@spec {| specification comment |}]
    |output}]
