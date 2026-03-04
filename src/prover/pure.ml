open Core.Syntax

let deep_destruct_conj t =
  let rec visit t acc =
    match t with
    | True -> acc
    | Conj (t1, t2) -> visit t1 (visit t2 acc)
    | _ -> t :: acc
  in
  visit t []
