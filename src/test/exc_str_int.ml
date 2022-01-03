
effect Exc : (string -> int)

let safediv x y ()  =
  if y == 0
  then perform Exc ("divide by zero\n")
  else x / y

let catch action h =
  match action () with 
  | n -> n
  | effect Exc k -> 
    continue k (fun str -> h str)

let zerodiv x y = 
  catch 
  (safediv x y) 
  (fun str -> print_string (str); (0))
  

let main = zerodiv 4 0

