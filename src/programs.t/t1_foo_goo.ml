effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo()).Goo.Q(Goo()) @*)
  = perform Foo ();
    perform Goo ()


let res : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.Goo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> ())
  | effect Goo k ->  continue k (fun () -> ())
