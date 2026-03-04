effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()) @*)
  = perform Foo ()

let res 
  (*@ requires _^* @*)
  (*@ ensures  Foo @*)
  =
  match f () with
  | _ -> perform Goo ()
  | effect Foo k ->  continue k (fun () -> ())
