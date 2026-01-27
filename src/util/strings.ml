module SMap = Map.Make (String)

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'
let code_of_quote = Char.code '\''
let code_of_underscore = Char.code '_'

let draw_line n =
  let unicode = true in
  match unicode with
  | true -> String.concat "" (Lists.make n "─")
  | false -> String.make n '-'

let cut_ident skip_quote s =
  let slen = String.length s in
  (* [n'] is the position of the first non nullary digit *)
  let rec numpart n n' =
    if n = 0 then
      (* ident made of _ and digits only [and ' if skip_quote]: don't cut it *)
      slen
    else
      let c = Char.code (String.get s (n - 1)) in
      if c = code_of_0 && n <> slen then numpart (n - 1) n'
      else if code_of_0 <= c && c <= code_of_9 then numpart (n - 1) (n - 1)
      else if skip_quote && (c = code_of_quote || c = code_of_underscore) then
        numpart (n - 1) (n - 1)
      else n'
  in
  numpart slen slen

let repr_ident s =
  let numstart = cut_ident false s in
  let slen = String.length s in
  if numstart = slen then (s, None)
  else (String.sub s 0 numstart, Some (int_of_string (String.sub s numstart (slen - numstart))))

let make_ident s = function
  | None -> s
  | Some n ->
      let c = Char.code (String.get s (String.length s - 1)) in
      let n = string_of_int n in
      if c < code_of_0 || c > code_of_9 then s ^ n else s ^ "_" ^ n
