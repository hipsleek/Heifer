effect Foo : (unit -> unit)
effect Goo : int-> (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  true /\ Koo!.Goo!.Goo?().Foo?() /\ ret = () @*)
  = let a = perform Foo in  
    let b = perform (Goo 5) in 
    b(); a()


let res 
  (*@ requires _^* @*)
  (*@ ensures  Koo!.Goo @*)
  =
  match f () with // Koo!.Goo
  | _ -> ()
  | effect (Foo) k ->  continue k (fun () -> ())
  | effect (Goo n ) k -> continue k (fun () -> ())

let main = 
  (*@ requires _^* @*)
  (*@ ensures  Koo.S! @*)
  match res () with 
  | effect Koo k -> 1 