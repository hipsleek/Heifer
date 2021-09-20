effect Foo : (int -> int)
 

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo 1) @*)
= perform Foo 1


let res ()
(*@ requires emp @*)
(*@ ensures  Foo^w @*)
=
  match f () with
  | x -> x
  | effect Foo k ->
     continue k (fun _ -> perform Foo 1)
