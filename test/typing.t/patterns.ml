
type size = Small | Medium | Large | Unbounded

let int_to_size n =
  match n with
  | x when x <= 100 -> Small
  | x when 101 <= x && x <= 1000 -> Medium
  | x when 1001 <= x -> Large
  | _ -> Unbounded

(* workaround, since the parser does not support data constructors yet *)
let[@pure] medium () = Medium
let[@pure] large () = Large

let is_medium x =
  (*@ ens res=medium(()) @*)
  int_to_size 500

let is_large_false x =
  (*@ ens res=large(()) @*)
  int_to_size 500

