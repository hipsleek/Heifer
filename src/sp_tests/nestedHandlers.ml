effect E : int 
effect F : string 

let foo () 
(*@  requires (true, _^* ) @*)
(*@  ensures  (true, F) @*)
= perform F

let bar () 
(*@  requires (true, _^* ) @*)
(*@  ensures  (true, F) @*)
=
  match foo () with 
  | x -> x 
  | effect E k -> (failwith "impossible")

let baz () 
(*@  requires (true, _^* ) @*)
(*@  ensures  (true, emp) @*)
=
  match bar () with 
  | x -> x 
  | effect F k -> continue k ("Hello, world!")

let main
(*@  requires (true, emp) @*)
(*@  ensures  (true, emp) @*)
= 
  print_string ((baz ()) ^"\n")
