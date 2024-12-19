effect Map : ('a -> 'b) * 'a array -> 'b array

let map_array (f, arr) 
=
  perform (Map (f, arr))

let map_handler ()
= 
  let foo x = x * 2 in
  let arr = [|1; 2; 3; 4; 5|] in
  match map_array (foo, arr) with
  | v -> v
  | effect (Map (f, arr)) k -> 
    let new_arr = (Array.map f arr) in 
    (continue k new_arr);
