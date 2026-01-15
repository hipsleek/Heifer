open Effect
open Effect.Deep

type _ Effect.t += Filter : ('a -> bool) * 'a list -> 'a list t

let filter_array (pred, arr) 
=
  perform (Filter (pred, arr))

let filter_handler () 
=
  let is_even x = x mod 2 = 0 in
  let arr = [1; 2; 3; 4; 5] in

  match_with filter_array (is_even, arr)
  { retc = (fun v -> v);
    exnc = raise;
    effc = fun (type a) (eff: a t) ->
      match eff with
      | Filter (pred, arr) -> Some (fun (k: (a, _) continuation) ->
          let new_arr = List.filter pred arr in
          (continue k new_arr);
          
          )
      | _ -> None }