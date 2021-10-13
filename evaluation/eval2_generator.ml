
let n = 3

let declear i= "effect Foo" ^ string_of_int i ^ " : (unit -> unit)\n" 

let declear0ToN =
  let rec aux i acc = 
    if i = 0 then  declear i ^ acc
    else aux (i-1) (declear i ^ acc)
  in 
  aux (n - 1) ""

let fun_prefix = 
  let rec aux i acc = 
    if i >= (n/2) then acc ^ "Foo" ^ string_of_int i
    else "(" ^ aux (2*i+1) (acc ^ "Foo" ^ string_of_int i ^".") ^ ") \\/ (" ^
         aux (2*i+2) (acc ^ "Foo" ^ string_of_int i ^".") ^ ")"
in 
"
let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)\n"  ^
"(*@ ensures  (" ^ aux 0  "" ^ ") @*)\n" ^
"  = match f () with
 | _ -> ()\n"


let match_body i = 
" | effect Foo" ^  string_of_int i ^ " k -> \n continue k (fun () -> if true then perform Foo" 
^ string_of_int ((2*i)+1) ^ "() else perform Foo"^ string_of_int ((2*i)+2) ^" ())\n"

let fun_match = 
  let rec aux i acc = 
    if i >= n then acc 
    else if i >= (n/2) then aux (i+1) (acc ^ (" | effect Foo" ^  string_of_int i ^ " k ->  continue k (fun () -> ())\n" ))
    else aux (i+1) (acc ^match_body i )
  in aux 0 ""


let main = 
  let temp = declear0ToN ^ fun_prefix ^ fun_match in 
  print_string (temp)