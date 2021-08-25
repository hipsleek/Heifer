effect Foo : (int -> int)
effect Goo : (int -> int)

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
     continue k (fun _ -> if 1 then perform Goo 1 else perform Foo 1;)
  | effect Goo k ->
      continue k (fun _ -> perform Goo 1;)

(*  ensures Foo.Q(Foo()) where Q(Foo_) = Foo *)