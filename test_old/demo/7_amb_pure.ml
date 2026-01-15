(* McCarthy's locally angelic choice operator (angelic modulo nontermination). *)
(* The following examples are adapted from Oleg Kiselyov
   "Non-deterministic choice amb"
   (c.f. https://okmij.org/ftp/ML/ML.html#amb) *)

effect Choose : bool list -> bool
effect Success : int -> unit 
effect Failure : int -> int 

let amb (xs:bool list) counter : bool
= let b = perform (Choose xs) in counter := !counter +1; b

let f xs counter = if amb xs counter then 7 else perform (Failure 500)

let handle (xs : bool list) counter : int 
= match (f xs counter) with
| x -> x 
| effect (Choose xs) k -> 
  match List.iter (fun ele -> 
   match let seven = resume k ele in perform (Success seven) with
   | effect (Success x) k -> perform (Success x)
   | effect (Failure _) k -> () (* Omitting Failure 500 *)
   | _ -> () 
   ) xs; (* iterate the lambda elements from xs *)
   perform (Failure 404)
  with | x -> x | effect (Success r) k -> r (* Leaking Failure 404 *)


effect Choose : bool list -> bool
effect Success : int -> unit 
effect Failure : int -> int 

let amb (xs:bool list) counter : bool
= let b = perform (Choose xs) in counter := !counter +1; b

let f xs counter = if amb xs counter then 7 else perform (Failure 500)

let handle (xs : bool list) counter : int 
= match (f xs counter) with
| x -> x 
| effect (Choose xs) k -> 
  match List.iter (fun ele -> 
   match let seven = continue k ele in perform (Success seven) with
   | effect (Success x) k -> perform (Success x)
   | effect (Failure _) k -> () (* Omitting Failure 500 *)
   | _ -> () 
   ) xs; (* iterate the lambda elements from xs *)
   perform (Failure 404)
  with | x -> x | effect (Success r) k -> r (* Leaking Failure 404 *)
   

let branch_example_generic (xs: (bool) list) counter : int
= handle xs counter

let _ =
  let counter  = ref 0 in
  let v = branch_example_generic [(false ); (false); (true); (false)] counter in
  Printf.printf "(%d)\n%!" v;
  Printf.printf "(counter = %d)\n%!" !counter
