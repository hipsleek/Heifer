
effect Foo : unit -> unit
effect Goo : unit -> unit


let f () 
(*@  requires (true, Foo(1)?1, 1)   @*)
(*@  ensures (true, _, 1) \/ (true, _, 1) @*)
= 
  print_string ("Foo ()\n");
  perform (Foo ())

let g () = 
  print_string ("Goo ()\n");
  perform (Goo ())

let test () = 
  f (); 
  print_string ("in the middle \n");
  g ()


let rec handle () = 
  match test() with 
  | _ -> print_string ("Done\n");()
  | effect (Foo _) k -> print_string ("before Foo\n"); continue k (); print_string ("after Foo\n")
  | effect (Goo _) k -> print_string ("before Goo\n"); continue k (); print_string ("after Goo\n")

   
let main = handle ()
(* Foo().Goo() *)