effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

ES= emp /\ SIDE = Eff(f):: A -> B^* 

let f () 
(*@ requires Eff(f):: A -> B^*  @*)
(*@ ensures  Foo.Q(Foo()).Goo.Q(Goo()) @*)
  = perform Foo ();
    perform Goo ();
    a


let res : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.Goo.Goo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> perform Goo ())
  | effect Goo k ->  continue k (fun () -> ())
