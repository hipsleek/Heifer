effect Foo : (unit -> int)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo @*)
  = perform Foo ()


let res () : int
  (*@ requires emp @*)
  (*@ ensures  Foo @*)
  =
  match f () with
  | x -> 1
  | effect Foo k ->
     continue k (fun () -> 1)
