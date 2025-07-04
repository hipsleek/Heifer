
type ball = Solid | Striped

type 'a llist = Cons of 'a * 'a llist | Nil

let rec foldr f ls init =
  match ls with
  | Nil -> init
  | Cons (x, xs) -> f x (foldr f xs init)

let rec exists ls f =
  foldr (fun v acc -> f v || acc) ls false

let[@pure] rec has_solid (ls : ball llist) : bool =
  match ls with
  | Nil -> false
  | Cons (Solid, xs) -> true
  | Cons (Striped, xs) -> has_solid xs

let exists_solid ls
  (*@ ens res = has_solid(ls) @*)
  =
    exists ls (fun o -> match o with | Solid -> true | Striped -> false)

let exists_striped_false ls
  (*@ ens res = has_solid(ls) @*)
  =
    exists ls (fun o -> match o with | Solid -> false | Striped -> true)

(* tests _ patterns, and previous pattern exclusion *)
let rec no_solids_aux ls =
match ls with
  | Cons (Solid, _) -> false
  | Cons (_, xs) -> no_solids_aux xs
  | _ -> true

(* split the verification condition out to a separate function since otherwise,
   no recursive definition is created for no_solids at proof time *)
let no_solids ls =
  (*@ ens res = ~has_solid(ls) @*)
  no_solids_aux ls
