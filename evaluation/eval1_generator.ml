
let n = 70

let declear i= "effect Foo" ^ string_of_int i ^ " : (unit -> unit)\n" 

let declear0ToN =
  let rec aux i acc = 
    if i = 0 then  declear i ^ acc
    else aux (i-1) (declear i ^ acc)
  in 
  aux (n - 1) ""

let fun_prefix = 
  let rec aux i acc  =
    if i = n then acc ^ "Foo0"
    else aux (i+1) (acc ^ "Foo" ^ string_of_int i ^".")
in 
"
let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)\n"  ^
"(*@ ensures  Foo0.(" ^ aux 1  "" ^ ")^w @*)\n" ^
"  = match f () with
 | _ -> ()\n"


let match_body i = 
" | effect Foo" ^  string_of_int i ^ " k ->  continue k (fun () -> perform Foo" 
^ string_of_int (i+1) ^ " ())\n"

let fun_match = 
  let rec aux i acc = 
    if i = (n -1) then acc ^ (" | effect Foo" ^  string_of_int i ^ " k ->  continue k (fun () -> perform Foo" 
    ^ string_of_int (0) ^ " ())\n")
    else aux (i+1) (acc ^match_body i )
  in aux 0 ""


let main = 
  let temp = declear0ToN ^ fun_prefix ^ fun_match in 
  print_string (temp)