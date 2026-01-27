module SMap = Map.Make (String)

let get_last s = s.[String.length s - 1]

let draw_line n =
  let unicode = true in
  match unicode with
  | true -> String.concat "" (Lists.make n "─")
  | false -> String.make n '-'
