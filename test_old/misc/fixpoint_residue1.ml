effect Foo : (unit -> int)
effect Goo : (unit -> int)
effect Koo : (unit -> int)

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo ()) @*)
= perform Foo () 



let res_f ()
  (*@ requires emp @*)
  (*@ ensures Foo.Goo.Q(Goo ()).Koo.Q(Koo ())  @*)
  =
  match (f ()) with
  | x -> perform Goo  ()
  | effect Foo k ->
      continue k (fun _ ->  () ); perform Koo  ()

let main
  (*@ requires emp @*)
  (*@ ensures  Foo.Goo.Koo  @*)
= match res_f () with 
  | _ -> ()
  | effect Goo k ->
  continue k (fun _ -> () )
  | effect Koo k ->
  continue k (fun _ -> () )

