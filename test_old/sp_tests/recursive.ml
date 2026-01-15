effect Yield : int -> unit 
effect Done : unit

let rec traverse (n:int) = 
  if n ==0 then perform Done
  else perform (Yield n); 
       traverse (n-1) 

let rec traverse1 (xs:int list) 
= match xs with
  | [] -> perform Done
  | x::xs -> perform (Yield x); traverse1 xs 

let main 
= match traverse (4) with 
  | v -> v
  | effect Done k -> ()
  | effect (Yield v) k -> 
    print_string (string_of_int v^"\n");
    continue k ()

  
