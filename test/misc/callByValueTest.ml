effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()).Goo.Q(Goo()) @*)
  = perform Foo ();
    perform Goo ()


let res 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo.Foo.Q(Foo()) @*)
  =
  match f () with
  | _ -> print_string("normal\n") ; ()
  | effect Foo k ->  continue k (fun () -> ()); perform Foo () ;
  | effect Goo k ->  continue k (fun () -> ()); print_string("goo\n") ;
