effect Foo : (int -> int)

effect Goo : (int -> int)

let f n 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo (n+1)) @*)
= perform Foo (n +1)

let res : int
  (*@ requires emp @*)
  (*@ ensures  (Foo.Goo)^w @*)
  =
  match f 0 with
  | _ -> 1
  | effect Foo k ->
     continue k (fun n -> perform Goo (n+1))
  | effect Goo k ->
     continue k (fun n -> perform Foo (n+1))

