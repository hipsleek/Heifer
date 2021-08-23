effect Foo : (int -> int)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo 1) @*)
= let a = perform Foo 1 in 
  a 


let res_f
  (*@ requires emp @*)
  (*@ ensures Foo^w  @*)
  =
  match (f ()) with
  | x -> x
  | effect Foo k ->
     continue k (fun _ -> perform Foo 1)

(*  ensures Foo.Q(Foo()) where Q(Foo_) = Foo *)