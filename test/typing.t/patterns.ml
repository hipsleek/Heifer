
type size = Small | Medium | Large | Unbounded

let int_to_size n =
  match n with
  | x when x <= 100 -> Small
  | x when 101 <= x && x <= 1000 -> Medium
  | x when 1001 <= x -> Large
  | _ -> Unbounded

let is_medium x =
  (*@ ens res=Medium @*)
  int_to_size 500

let is_large_false x =
  (*@ ens res=Large @*)
  int_to_size 500

