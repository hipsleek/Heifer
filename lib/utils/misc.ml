let ( let@ ) f x = f x

let string_of_pair pa pb (a, b) = Format.asprintf "(%s, %s)" (pa a) (pb b)

let string_of_list p xs =
  match xs with
  | [] -> "[]"
  | _ ->
    let a = List.map p xs |> String.concat "; " in
    Format.asprintf "[%s]" a

let string_of_list_lines p xs =
  match xs with
  | [] -> ""
  | _ ->
    List.map p xs |> String.concat "\n"

let indent s =
  String.split_on_char '\n' s
  |> List.map (fun l -> "  " ^ l)
  |> String.concat "\n"

let string_of_list_ind_lines p xs =
  indent (string_of_list_lines p xs)

let quote = Format.asprintf "\"%s\""

let protected f finally = Fun.protect ~finally f

let todo () = failwith "todo"
