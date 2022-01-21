

effect Foo : (unit -> unit)
effect Goo : (unit -> unit)
effect Koo : (unit -> unit)
effect Zoo : (unit -> unit)

let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()) @*)
  = print_string ("Foo\n");
    perform Foo ()



let res11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo^* @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> perform Foo ())

let res12 ()
  (*@ requires _^* @*)
  (*@ ensures  Foo.((Goo.Foo)^* ) @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  print_string ("Koo\n");  perform Koo (); continue k (fun () -> print_string ("Goo\n"); perform Goo ())
  | effect Goo k ->  print_string ("Zoo\n");  perform Zoo (); continue k (fun () -> print_string ("Foo\n");  perform Foo ())

let test =
  match res12 () with 
  | _ -> ()
  | effect Koo k ->  continue k (fun () ->  ())
  | effect Zoo k -> continue k (fun () ->  ())

