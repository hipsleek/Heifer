effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
  requires emp
  ensures  Foo
= perform Foo ()


let res
  requires emp
  ensures  Foo^w
  =
  match f () with
  | x -> ()
  | effect Foo k ->
     continue k (fun () -> perform Foo ())
  | effect Goo k ->
     continue k (fun () -> ())

