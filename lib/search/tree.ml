open Printf

let red text = "\u{001b}[31m" ^ text ^ "\u{001b}[0m"

let rec iter f = function
  | [] -> ()
  | [x] -> f true x
  | x :: tl ->
    f false x;
    iter f tl

let to_buffer ?(line_prefix = "") ~get_ornament ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      Format.asprintf
        (if is_last then "%s└─ " else "%s├─ ")
        (match get_ornament x with Some s -> s | None -> " ")
    in
    bprintf buf "%s%s" indent line;
    let extra_indent = if is_last then "    " else " │  " in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_ornament ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_ornament ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string option * string * binary_tree list
  | Leaf

let get_name = function Leaf -> "." | Node (_o, name, _) -> name

let get_children = function
  | Leaf -> []
  | Node (_o, _, li) -> List.filter (( <> ) Leaf) li

let get_ornament = function Leaf -> None | Node (o, _, _) -> o

let rule ?(children = []) ?(success = true) ~name fmt =
  Format.kasprintf
    (fun s ->
      Node
        ( Some "r",
          Format.asprintf "[%s]%s %s" name
            (if success then "" else red " FAIL")
            s,
          children ))
    fmt

type proof = binary_tree

let string_of_proof tree =
  printTree ~line_prefix:"│" (* ~line_prefix:" " *) ~get_ornament ~get_name
    ~get_children tree
