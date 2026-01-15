effect Zero: int

let rec times lst = 
  match lst with 
  | [] -> 1
  | 0 :: rest -> perform Zero
  | v :: rest -> v * times rest  

let handler () = 
  match times [1;2;3;4;5] with 
  | v -> v 
  | effect Zero k -> 0 
  
let main = 
  print_string (string_of_int (handler ()) ^ "\n")