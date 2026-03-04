effect Choose : (string * float)

let choose () = perform Choose

let flip_compose (a, b) (c, d) = (a ^ c, b*.d) 

let rec pretty_print li : string = 
  match li with 
  | [] -> ""
  | (a, _) :: xs  -> "\"" ^ a  ^ "\"," ^ pretty_print xs 

  
let rec pretty_print1 li : string = 
  match li with 
  | [] -> ""
  | (_, p) :: xs  -> string_of_float p ^ ", " ^ pretty_print1 xs 

  
let rec toss n : (string * float)
= if n == 0 then ("", 1.0)
  else flip_compose (choose ()) (toss (n-1)) 

let all_results () 
= match toss 3 with
  | v -> [v]
  | effect Choose k -> 
      (continue k ("0", 0.1)) 
      @
      (continue (Obj.clone_continuation k) ("1", 0.9))

let main = 
  let res = all_results () in 
  print_endline (pretty_print(res));
  print_endline (pretty_print1(res ))

