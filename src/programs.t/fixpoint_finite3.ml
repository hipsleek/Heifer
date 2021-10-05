effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Goo.Q(Goo()).Q(Foo()) @*)
  = let a = perform Foo in  
    let b = perform Goo in 
    b(); a()


let res 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> ())
  | effect Goo k ->  continue k (fun () -> ())
