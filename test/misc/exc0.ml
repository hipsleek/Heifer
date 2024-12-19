
exception Exc of string

let safediv x y =
  if y == 0
  then raise (Exc ("divide by zero\n"))
  else x / y

let catch  =
  match safediv 4 0 with 
  | n -> n
  | exception Exc str -> (print_string (str); 0)
