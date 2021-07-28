effect Foo : (unit -> 'a)


let f () 
  requires emp
  ensures Foo
= perform Foo ()

let res : type a. a 
  (*@ requires emp @*)
  (*@ ensures  Foo^w @*)
  =
  match f () with
  | x -> x
  | effect Foo k ->
     continue k (fun () -> perform Foo ())
  [@@requires emp]
  [@@ensures Foo^w]
