effect Foo : (unit )
effect Goo : (unit )
effect Zoo : (unit )

let print_and_perform_Goo () = 
  (*@ requires emp @*)
(*@ ensures  Goo @*)
  print_string ("Goo\n") ;perform Goo

let print_and_perform_Foo () = 
  (*@ requires emp @*)
(*@ ensures  Foo.Goo @*)
  print_string ("Foo\n") ;perform Foo; print_and_perform_Goo ()

let print_and_perform_Goo1 () = 
  print_string ("Goo1\n") ;perform Goo

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Goo @*)
  = print_and_perform_Foo ();
    print_and_perform_Goo ()

let res : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.Zoo.Goo @*)
  =
  match f () with
  | _ -> print_string ("finished\n"); ()
  | effect Foo k ->  perfrom Zoo; continue k (())
  | effect Goo k ->  continue k (())


