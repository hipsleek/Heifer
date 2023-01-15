effect E : int 
effect F : string 

let foo () 
(*@ requires _^*  @*)
(*@ ensures F @*)
= perform F

let bar () 
(*@ requires _^*  @*)
(*@ ensures F @*)
=
  match foo () with 
  | x -> x 
  | effect E k -> (failwith "impossible")

let baz () 
(*@ requires _^*  @*)
(*@ ensures emp @*)
=
  match bar () with 
  | x -> x 
  | effect F k -> continue k ("Hello, world!")

let main = 
  print_string (baz () ^"\n")
