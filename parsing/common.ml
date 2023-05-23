let rec split_last xs =
  match xs with
  | [] -> failwith "split_last"
  | [x] -> ([], x)
  | x :: xs ->
    let init, last = split_last xs in
    (x :: init, last)

let dbg_none = 0
let dbg_info = 1
let dbg_debug = 2
let debug_level = ref dbg_none

let debug fmt =
  Format.kasprintf
    (fun s ->
      if !debug_level >= dbg_debug then print_string s;
      flush stdout)
    fmt

let info fmt =
  Format.kasprintf
    (fun s ->
      if !debug_level >= dbg_info then print_string s;
      flush stdout)
    fmt

let rec replace_nth n y xs =
  match (n, xs) with
  | 0, [] -> []
  | 0, _ :: xs -> y :: xs
  | _, [] -> []
  | _, x :: xs1 -> x :: replace_nth (n - 1) y xs1
