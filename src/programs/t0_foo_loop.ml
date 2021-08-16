effect Foo : (unit -> 'a)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo()) @*)
= perform Foo ()

let res_f
  (*@ requires emp @*)
  (*@ ensures Foo^w  @*)
  =
  match f () with
  | x -> x
  | effect Foo k ->
     continue k (fun () -> perform Foo ())
