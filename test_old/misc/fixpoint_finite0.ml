effect Foo : (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()) @*)
  = perform Foo ()

let res 
  (*@ requires _^* @*)
  (*@ ensures  Foo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> ())
