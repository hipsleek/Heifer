
effect Exc : int

let safediv x y ()  =
  if y == 0
  then perform Exc 
  else x / y

let catch action =
  match action () with 
  | effect Exc k -> 
    continue k (-1)

let zerodiv x y = 
  catch 
  (safediv x y) 

let main = 
  let res = zerodiv 4 0 in 
  print_string (string_of_int res^"\n")



