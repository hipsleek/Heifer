effect E : int 
effect F : string 

let foo () 
(*@  requires (true, _^* , ()) @*)
(*@  ensures  (true, F, ()) @*)
= perform F

let bar () 
(*@  requires (true, _^* , ()) @*)
(*@  ensures  (true, F, x ) @*)
=
  match foo () with 
  | x -> x 
  | effect E k -> (failwith "impossible")

let baz () 
(*@  requires (true, _^* , ()) @*)
(*@  ensures  (true, emp, 1) @*)
=
  match bar () with 
  | x -> x 
  | effect F k -> continue k 1

let main
= 
  print_string ((baz ()) ^"\n")
