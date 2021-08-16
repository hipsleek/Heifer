effect Foo : (unit -> 'a)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo()) @*)
= perform Foo ()
  raise Res 

let res_f
  (*@ requires emp @*)
  (*@ ensures Foo^w  @*)
  ensures Foo.Q(Foo()) where Q(Foo_) = Foo

  =
  match f () with
  | x -> x
  | effect Foo k ->
     continue k (fun () -> perform Foo ())
