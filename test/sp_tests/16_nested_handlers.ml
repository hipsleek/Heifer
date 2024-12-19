effect E: int 


let code () = 
  let x=perform E in
  x

let first_handler () = 
  match code () with 
  | v -> v + (perform E)
  | effect E k -> continue k 1

let second_handler () = 
  match first_handler () with 
  | v -> v 
  | effect E k -> continue k 2
  
let main  = 
  print_endline (string_of_int (second_handler ()))
