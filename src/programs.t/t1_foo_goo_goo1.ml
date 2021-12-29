effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Goo.Q(Goo()).Q(Foo()) @*)
  = let m = perform Foo in 
    let n = perform Goo in 
    n (); m ()



let res : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.Goo.Goo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> perform Goo ())
  | effect Goo k ->  continue k (fun () -> ())
