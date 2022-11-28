effect Foo : (unit -> int)
effect Goo : (unit -> int)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo ()) @*)
= perform Foo () 



let res_f ()
  (*@ requires emp @*)
  (*@ ensures Foo^w   @*)
  =
  match (f ()) with
  | x -> print_string ("Done1\n"); x 
  | effect Foo k -> 
      (match perform Goo () with
      | x -> () ); 
      print_string ("lallalall\n"); 0


let main = 
  match res_f () with 
  | x -> print_string ("Done\n"); x  
  | effect Goo k -> print_string ("Goo\n"); 1


      
