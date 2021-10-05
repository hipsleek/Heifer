effect Foo : (unit -> int)

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo ()) @*)
= perform Foo () 



let res_f
  (*@ requires emp @*)
  (*@ ensures Foo^w   @*)
  =
  match (f ()) with
  | x -> x
  | effect Foo k ->
      continue k (fun _ -> perform Foo () )
