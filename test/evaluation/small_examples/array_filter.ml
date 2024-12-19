effect Filter : ('a -> bool) * 'a array -> 'a array

let filter_array (pred, arr) 
=
  perform (Filter (pred, arr))

let filter_handler () 
=
  let is_even x = x mod 2 = 0 in
  let arr = [|1; 2; 3; 4; 5|] in
  match filter_array (is_even, arr) with
  | v -> v
  | effect (Filter (pred, arr)) k ->
    let new_arr = Array.filter pred arr in
    (continue k new_arr);