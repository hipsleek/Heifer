(* basic tests involving inductive constructor definitions *)

type traffic_light = Red | Yellow | Green

let step color =
  match color with
  | Red -> Yellow
  | Yellow -> Green
  | Green -> Red

let id color = color

let triple_step color =
  color |> step |> step |> step
(*@ ens res=color @*)

type inductive_int = Zero | Succ of inductive_int

let rec plus n m = match n with
  | Zero -> m
  | Succ n -> Succ (plus n m)

let add_zero n = plus Zero n
(*@ ens res=n @*)

type 'a opt = Just of 'a | Nothing

let rec exists ls f =
  match ls with
  | x::xs -> (f x) || exists xs f
  | [] -> false

let rec has_some ls =
  match ls with
  | (Just _)::_ -> true
  | Nothing::xs -> has_some xs
  | [] -> false

let rec exists_opt ls = 
  exists ls (fun o -> match o with
    | Just _ -> true
    | Nothing -> false)
(*@ ex ys; has_some(ls, ys); ens res=ys @*)

let has_some_2 ls =
  match ls with
  | (Just _)::_ -> true
  | Nothing::xs -> false
  | _ -> false

let rec exists_opt_false ls = 
  exists ls (fun o -> match o with
    | Just _ -> true
    | Nothing -> false)
(*@ ex ys; has_some_2(ls, ys); ens res=ys @*)
