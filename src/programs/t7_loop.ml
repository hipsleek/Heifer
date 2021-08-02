effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
  requires emp
  ensures  Foo.Foo
= perform Foo ();
  perform Foo ()


let res
  requires emp
  ensures  Foo
  =
  match f () with
  | x -> ()
  | effect Foo k ->
     continue k (fun () -> perform Goo ())
  | effect Goo k ->
     continue k (fun () -> perform Foo ())

