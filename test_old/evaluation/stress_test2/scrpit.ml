

let rec autogenerator n =
  if n > 1200 then ""
  else "ex x" ^ string_of_int n ^ "; Read(emp, x"
  ^ string_of_int n ^ "); ex r" ^ string_of_int n 
  ^ "; Write(emp, (x" ^ string_of_int n 
  ^ "+1), r" ^ string_of_int n  ^ ");\n" 
  ^ autogenerator (n+1)
  

let main = 
  print_endline (autogenerator 1)