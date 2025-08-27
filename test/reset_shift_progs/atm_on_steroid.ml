let [@spec "ens res = \"the answer is always: 42\""] main () =
  let f = reset (shift (fun k -> k)) in
  let i = f 42 in
  let s = f "the answer is always: " in
  let r = string_of_int i in
  s ^ r
