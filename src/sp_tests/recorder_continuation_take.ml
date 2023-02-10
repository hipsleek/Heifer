type fund_t = Found of int | NotFound 

effect: FoundIt : int

let rec loop (li: int list) (n: int) : (fund_t * int list) = 
  match li with 
  | [] -> (NotFound, [])
  | first :: rest -> 
    if n == 0 then (Found first, rest)
    else 
      let (f, l) = loop rest (n-1) in 
      (f, first :: l)

let rec loop1 (li: int list) (n: int) : (fund_t * int list) = 
  match li with 
  | [] -> []
  | first :: rest -> 
    if n == 0 then first :: perform FoundIt
    else 
      let (f, l) = loop rest (n-1) in 
      (f, first :: l)

let handler () = 
  match (loop1 [0;1;2;3;4;5] 3) with 
  | v ->  v
  | effect FoundIt k -> cnotinue k ()


let string_of_fund_t_int_list (f, l) = 
  (match f with 
  | Found i -> "Found "  ^ string_of_int i  ^ ", "
  | NotFound -> "NotFound," )
  ^ 
  List.fold_left (fun acc a -> acc ^ " " ^ string_of_int a) "" l 
  ^ "\n"

let main = 
  print_string (string_of_fund_t_int_list (loop [0;1;2;3;4;5] 0)); 
  print_string (string_of_fund_t_int_list (loop [0;1;2;3;4;5] 3)); 
  print_string (string_of_fund_t_int_list (loop [0;1;2;3;4;5] 7))
