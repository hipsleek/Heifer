

effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()).Foo.Q(Foo()) @*)
  = print_string ("Foo\n");
    perform Foo ();
    perform Foo ()



let res11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo^* @*)
  =
  match f () with
  | _ -> perform Goo ()
  | effect Foo k ->  continue k (fun () -> ()) 
