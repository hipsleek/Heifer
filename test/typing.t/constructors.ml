(* basic tests involving inductive constructor definitions *)

type traffic_light = Red | Yellow | Green

let step color =
  match color with
  | Red -> Yellow
  | Yellow -> Green
  | Green -> Red

let id color = color

let triple_step color 
(*@ ens res=color @*)
= step (step (step color))

let double_step_false color 
(*@ ens res=color @*)
= step (step color)

type inductive_int = Zero | Succ of inductive_int

let rec plus n m = match n with
  | Zero -> m
  | Succ n -> Succ (plus n m)

let add_zero n 
(*@ ens res=n @*)
= plus Zero n

(* an induction hypothesis is automatically inferred so this passes *)
let add_zero_2 n
(*@ ens res=n @*)
= plus n Zero

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
