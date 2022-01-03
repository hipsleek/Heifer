effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let print_and_perform_Foo () = 
  print_string ("Foo\n") ;perform Foo

let print_and_perform_Goo () = 
  print_string ("Goo\n") ;perform Goo

let print_and_perform_Goo1 () = 
  print_string ("Goo1\n") ;perform Goo

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Goo.Q(Goo()).Q(Foo()) @*)
  = let m = print_and_perform_Foo () in 
    let n = print_and_perform_Goo () in 
    n (); m ()

let res : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.Goo.Goo @*)
  =
  match f () with
  | _ -> print_string ("finished\n"); ()
  | effect Foo k ->  continue k (fun () -> (print_and_perform_Goo1 ()) ())
  | effect Goo k ->  continue k (fun () -> ())
