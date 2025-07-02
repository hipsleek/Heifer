
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
