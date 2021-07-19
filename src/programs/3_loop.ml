effect Foo : (int -> int)

effect Goo : (unit -> int)

effect Zoo : (unit -> int)

let f () 
(*@ requires emp @*)
(*@ ensures  Foo(1) @*)
  = perform Foo 1


let res : int
  (*@ requires emp @*)
  (*@ ensures  (Foo (_).Goo ().Foo (100))^w @*)
  Foo(1).Goo().(Foo(100).Goo())^w
  =
  match f () with
  | x -> 1
  | effect Foo k ->
     continue k (fun x -> perform Goo ())
// Foo (x) -> Goo ()
  | effect Goo k ->
     continue k (fun () -> perform Foo 100)
// Goo () -> Foo 100

1. parser 
2. infer 