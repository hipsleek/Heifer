effect Foo : (unit -> int)
effect Goo : (unit -> int)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo ()) @*)
= perform Foo () 



let res_f ()
  (*@ requires emp @*)
  (*@ ensures Foo.Goo.Q(Goo ())  @*)
  =
  match (f ()) with
  | x -> perform Goo  ()
  | effect Foo k ->
      continue k (fun _ ->  () )

let main
  (*@ requires emp @*)
  (*@ ensures  Foo.Goo  @*)
= match res_f () with 
  | _ -> ()
  | effect Goo k ->
  continue k (fun _ -> () )
