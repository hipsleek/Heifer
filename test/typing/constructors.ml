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

let rec foldr f ls init =
  match ls with
  | [] -> init
  | x::xs -> f x (foldr f xs init)

let rec exists ls f =
  foldr (fun v acc -> f v || acc) ls false

let rec has_red ls =
  match ls with
  | [] -> false
  | Red::_ -> true
  | _::xs -> has_red xs

(* these currently doesn't work *)
(* probably because the has_red spec isn't being unfolded *)

let exists_red ls
  (*@ ex ys. has_red(ls, ys); ens res=ys @*)
  =
    exists ls (fun o -> match o with | Red -> true | _ -> false)

