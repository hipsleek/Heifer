open Core.Syntax

let make_args uvars sigma =
  try Some (Array.map (fun x -> TVMap.find x sigma) uvars)
  with Not_found -> None
